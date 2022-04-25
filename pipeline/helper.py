import pathlib
import typing

from pycparser import c_ast
from pycparser.c_ast import *
from pycparser.c_generator import CGenerator


class ExprCapture(NodeVisitor):
    def __init__(self):
        self.exprs = set()

    def visit_BinaryOp(self, node: BinaryOp):
        self.exprs.add(node)
        NodeVisitor.generic_visit(self, node)

    def visit_UnaryOp(self, node: UnaryOp):
        self.exprs.add(node)
        NodeVisitor.generic_visit(self, node)

    def visit_FuncCall(self, node: UnaryOp):
        self.exprs.add(node)
        NodeVisitor.generic_visit(self, node)


class ContainsVariable(c_ast.NodeVisitor):
    def __init__(self, variables: typing.FrozenSet[str]):
        self.variables = variables
        self.found = False

    def visit_ID(self, node: ID):
        if node.name in self.variables:
            self.found = True


def input_pure(node: c_ast.Node, var_names: typing.List[str]):
    class IsPureVisitor(c_ast.NodeVisitor):
        def __init__(self):
            self.pure = True
            self.contains_var = False

        def visit_FunCall(self, node):
            self.pure = False

        def visit_ID(self, node):
            self.contains_var = True
            if node.name not in var_names:
                self.pure = False

    v = IsPureVisitor()
    v.visit(node)
    if v.pure and v.contains_var:
        return CGenerator().visit(node)


def cycleCheck(node: c_ast.Node, parents=None):
    if not parents:
        parents = []

    parents.append(node)

    for c in node:
        if c in parents:
            raise BaseException("CYCLE!")
        cycleCheck(c, parents)
    parents.remove(node)


def find(pred, seq):
    for tl in seq:
        if pred(tl): return tl
    return None


class SymbolicExecution(NodeVisitor):
    def __init__(self, cast: c_ast.FileAST):
        self.state: typing.Dict[str, str] = dict()
        self.defines: typing.Dict[str, c_ast.Node] = dict()
        self.count: typing.Dict[str, int] = dict()
        self.file_ast = cast

        self.init_global_state()
        self.call()

    def init_global_state(self):
        for c in self.file_ast:
            if isinstance(c, c_ast.Decl) and not isinstance(c.type, c_ast.FuncDecl):
                self.state[c.name] = c.name

    def call(self, func='main'):
        function = find(lambda x: isinstance(x, c_ast.FuncDef) and x.decl.name == func, self.file_ast.ext)
        if function:
            self.visit(function.body)
        else:
            raise BaseException(f"Could not find function {func}")

    def visit_FuncCall(self, node: c_ast.FuncCall):
        # No support for arguments at this point
        if node.args is not None:
            return node
        self.call(func=node.name.name)

    def visit_Constant(self, node: c_ast.Constant):
        return node

    def visit_Assignment(self, node: c_ast.Assignment):
        expr = NodeVisitor.visit(self, node.rvalue)
        name = node.lvalue.name
        ssa_name = self.fresh_ssa_name(name)
        self.defines[ssa_name] = expr
        self.state[name] = ssa_name

    def fresh_ssa_name(self, name):
        cnt = self.count.get(name, 0) + 1
        self.count[name] = cnt
        ssa_name = "%s_%04d" % (name, cnt)
        return ssa_name

    def visit_If(self, node: c_ast.If):
        cond = NodeVisitor.visit(self, node.cond)
        old = self.state

        self.state = old.copy()
        NodeVisitor.visit(self, node.iftrue)
        then = self.state

        other = self.state = old.copy()
        if node.iffalse is not None:
            NodeVisitor.visit(self, node.iffalse)
            other = self.state

        self.state = self.merge_states(cond, then, other)
        return None

    def visit_BinaryOp(self, node: c_ast.BinaryOp):
        left = NodeVisitor.visit(self, node.left)
        right = NodeVisitor.visit(self, node.right)
        return BinaryOp(node.op, left, right, node.coord)

    def visit_UnaryOp(self, node: c_ast.UnaryOp):
        expr = NodeVisitor.visit(self, node.expr)
        return UnaryOp(node.op, expr, node.coord)

    def visit_ID(self, node: c_ast.ID):
        if node.name in self.state:
            return c_ast.ID(self.state[node.name])
        else:
            return node

    def merge_states(self, cond, then, other):
        state = {}
        keys = set(then.keys()).union(other.keys())

        for k in keys:
            t = then[k]
            e = other[k]
            if t == e:
                state[k] = t
            else:
                ssa_name = self.fresh_ssa_name(k)
                self.defines[ssa_name] = c_ast.TernaryOp(cond, c_ast.ID(t), c_ast.ID(e))
                state[k] = ssa_name
        return state


class RenameingPrinter(CGenerator):
    def __init__(self, name_prefix: str):
        super().__init__()
        self.suffix = name_prefix

    def visit_ID(self, n):
        return f"{n.name}{self.suffix}"

    def visit_FuncCall(self, n):
        fref = self._parenthesize_unless_simple(n.name)
        return fref + '(' + self.visit(n.args) + ')'

    def visit_FuncDef(self, n):
        return super().visit_FuncDef(n)

    def visit_FuncDecl(self, n):
        return super().visit_FuncDecl(n)

    def visit_Decl(self, n: c_ast.Decl, no_type=False):
        nt = n.type
        if isinstance(nt, c_ast.TypeDecl):
            nt = c_ast.TypeDecl(nt.declname + self.suffix, nt.quals, nt.align, nt.type, nt.coord)
        elif isinstance(nt, c_ast.FuncDecl):
            a = nt.type
            nt = c_ast.FuncDecl(nt.args,
                                c_ast.TypeDecl(a.declname + self.suffix, a.quals, a.align, a.type, a.coord),
                                nt.coord)
        elif isinstance(nt, c_ast.ArrayDecl):
            a = nt.type
            nt = c_ast.ArrayDecl(c_ast.TypeDecl(a.declname + self.suffix, a.quals, a.align, a.type, a.coord),
                                 nt.dim, nt.dim_quals, nt.coord)
        else:
            print(">>> ERROR")

        new = c_ast.Decl(n.name + self.suffix,
                         n.quals, n.align, n.storage, n.funcspec, nt,
                         n.init, n.bitsize, n.coord)

        return super().visit_Decl(new, no_type)


class EmbeddingPrinter(CGenerator):
    def __init__(self, level, symex: SymbolicExecution):
        super().__init__()
        self.level = level
        self.symex = symex

    def visit_ID(self, n: c_ast.ID):
        name = n.name
        if self.level > 0 and name in self.symex.defines:
            return EmbeddingPrinter(self.level - 1, self.symex).visit(self.symex.defines[name])
        else:
            return super().visit_ID(n)


import click


class PPath(click.Path):
    """
    A Click path argument that returns a ``Path``, not a string.
    """

    def convert(
            self,
            value: str,
            param: click.core.Parameter | None,
            ctx: click.core.Context | None,
    ) -> typing.Any:
        """
        Return a ``Path`` from the string ``click`` would have created with
        the given options.
        """
        return pathlib.Path(super().convert(value=value, param=param, ctx=ctx))
