import pprint
import typing

from pycparser import c_ast
from pycparser.c_ast import *
import numpy as np
from .helper import find


class MemoryModel:
    def __init__(self):
        self.global_data: typing.Dict[str] = dict()
        self.stack: typing.List[typing.Dict[str]] = list(dict())

    def pop(self):
        del self.stack[-1]

    def push(self):
        self.stack.append(dict())

    def __setitem__(self, key: str, value):
        if key in self.global_data:
            self.global_data[key] = value
        else:
            self.stack[-1][key] = value

    def __getitem__(self, item: str):
        try:
            return self.stack[-1][item]
        except KeyError:
            return self.global_data[item]


def is_concrete(value):
    return not isinstance(value, c_ast.Node)


def eval_binary(op, left, right):
    match op:
        case "+":
            return left + right
        case "*":
            return left * right
        case "%":
            return left % right
        case "-":
            return left - right
        case "/":
            return left / right
        case "+":
            return left + right
        case "<":
            return left < right
        case "<=":
            return left <= right
        case ">":
            return left > right
        case ">=":
            return left >= right
        case "==":
            return left == right
        case "!=":
            return left != right
        case "&&":
            return left and right
        case "||":
            return left or right
        case "&":
            return left & right
        case "|":
            return left | right
        case "<<":
            return left << right
        case ">>":
            return left >> right
        case _:
            assert False


def _eval_unary(op, value):
    match op:
        case "!":
            return not value
        case "-":
            return - value
        case "+":
            return value
        case _:
            assert False


class ExpressionRewriter(NodeVisitor):
    def __init__(self, memory, config):
        self.memory = memory
        self.config = config

    # def visit_Cast(self, node: c_ast.Cast):
    #    return NodeVisitor.visit(self, node.expr)
    #    match node.to_type.name:
    #        case _: return value

    # def visit_FuncCall(self, node: c_ast.FuncCall):
    #     self.memory.push()
    #     # No support for arguments at this point
    #     if node.args is not None:
    #         return node
    #     self.call(func=node.name.name)
    #     self.memory.pop()

    def visit_Constant(self, node: c_ast.Constant):
        if node.type == 'int':
            return np.int32(node.value)
        elif node.type == 'boolean':
            return "true" == node.value
        elif node.type == 'float':
            return np.int32(node.value) # np.float(node.value)
        else:
            assert False

    def visit_BinaryOp(self, node: c_ast.BinaryOp):
        left = NodeVisitor.visit(self, node.left)
        right = NodeVisitor.visit(self, node.right)

        if is_concrete(left) and is_concrete(right):
            return eval_binary(node.op, left, right)
        else:
            n_left = left if not is_concrete(left) else Constant("int", value=left)
            n_right = right if not is_concrete(right) else Constant("int", value=right)
            return BinaryOp(node.op, n_left, n_right)

    def visit_ArrayRef(self, node: c_ast.ArrayRef):
        idx = NodeVisitor.visit(self, node.subscript)
        ary = self.memory[node.name.name]
        return ary[int(idx)]

    def visit_UnaryOp(self, node: c_ast.UnaryOp):
        value = NodeVisitor.visit(self, node.expr)
        if is_concrete(value):
            return _eval_unary(node.op, value)
        else:
            return node

    def visit_ID(self, node: c_ast.ID):
        if node.name in self.config['INPUTS']:
            return node
        else:
            return self.memory[node.name]


class Evaluator(NodeVisitor):
    def __init__(self, cast: c_ast.FileAST, config):
        self.config = config
        self.memory = MemoryModel()
        self.file_ast = cast
        self.computation_trace: typing.List[c_ast.Node] = []
        self.expr_rewriter = ExpressionRewriter(self.memory, self.config)

        self.memory.push()
        self.init_global_state()
        self.init_input()
        self.call()

    def visit_InitList(self, node: InitList):
        ary = list()
        for e in node.exprs:
            ary.append(NodeVisitor.visit(self, e))
        return ary


    def init_global_state(self):
        for c in self.file_ast:
            if isinstance(c, c_ast.Decl) and not isinstance(c.type, c_ast.FuncDecl):
                if c.init is not None:
                    v = self.visit(c.init)
                    assert (v is not None, f"{c.init}")
                    self.memory.global_data[c.name] = v
                    print(f">>> Assign {c.name} = {v}")
                else:
                    match c.type.type:
                        case IdentifierType(names=['int']):
                            self.memory.global_data[c.name] = np.int32(0)
                        case _:
                            assert False;

    def visit_Cast(self, node: c_ast.Cast):
        value = NodeVisitor.visit(self, node.expr)
        match node.to_type.name:
            case _: return value

    def call(self, func='main'):
        function = find(lambda x: isinstance(x, c_ast.FuncDef) and x.decl.name == func, self.file_ast.ext)
        if function:
            self.visit(function.body)
        else:
            raise BaseException(f"Could not find function {func}")

    def visit_FuncCall(self, node: c_ast.FuncCall):
        self.memory.push()
        # No support for arguments at this point
        if node.args is not None:
            return node
        self.call(func=node.name.name)
        self.memory.pop()

    def visit_Constant(self, node: c_ast.Constant):
        if node.type == 'int':
            return np.int32(node.value)
        elif node.type == 'boolean':
            return "true" == node.value
        elif node.type == 'float':
            return np.int32(node.value) # np.float(node.value)
        else:
            assert False

    def visit_Assignment(self, node: c_ast.Assignment):
        svalue = self.expr_rewriter.visit(node.rvalue)

        self.computation_trace.append(
            Assignment(node.op, node.lvalue,
                       svalue if not is_concrete(svalue) else Constant('int', svalue)))

        value = np.int32( NodeVisitor.visit(self, node.rvalue) )
        name = node.lvalue.name
        self.memory[name] = value
        print(f"Execute assignment {name} = {value} {type(value)} ({node.coord})")

    def visit_If(self, node: c_ast.If):
        cond = NodeVisitor.visit(self, node.cond)
        s_cond = self.expr_rewriter.visit(node.cond)
        s_cond = s_cond if not is_concrete(s_cond) else Constant('int', str(s_cond))
        if cond:
            self.computation_trace.append(c_ast.FuncCall(ID("assume"), s_cond))
            NodeVisitor.visit(self, node.iftrue)
        elif node.iffalse:
            self.computation_trace.append(c_ast.FuncCall(ID("assume"), c_ast.UnaryOp("!", s_cond)))
            NodeVisitor.visit(self, node.iffalse)

    def visit_BinaryOp(self, node: c_ast.BinaryOp):
        left = NodeVisitor.visit(self, node.left)
        right = NodeVisitor.visit(self, node.right)

        match node.op:
            case "+":
                return left + right
            case "*":
                return left * right
            case "%":
                return left % right
            case "-":
                return left - right
            case "/":
                return left / right
            case "+":
                return left + right
            case "<":
                return left < right
            case "<=":
                return left <= right
            case ">":
                return left > right
            case ">=":
                return left >= right
            case "==":
                return left == right
            case "!=":
                return left != right
            case "&&":
                return left and right
            case "||":
                return left or right
            case "&":
                return left & right
            case "|":
                return left | right
            case "<<":
                return left << right
            case ">>":
                return left >> right
            case _:
                assert False;

    def visit_UnaryOp(self, node: c_ast.UnaryOp):
        value = NodeVisitor.visit(self, node.expr)
        match node.op:
            case "!":
                return not value
            case "-":
                return - value
            case "+":
                return value
            case _:
                assert False

    def visit_ID(self, node: c_ast.ID):
        return self.memory[node.name]

    def visit_ArrayRef(self, node: c_ast.ArrayRef):
        idx = NodeVisitor.visit(self, node.subscript)
        ary = self.memory[node.name.name]
        return ary[int(idx)]

    def init_input(self):
        for var, value in self.config['INPUTS'].items():
            if value:
                v = np.int32(value)
                self.memory.global_data[var] = v
                print(f">>> Assign by input {var} = {v}")
