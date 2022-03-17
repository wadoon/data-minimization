#!/usr/bin/python
import os
import re
import sys
import typing
from typing import FrozenSet

import pycparser

import stackprinter
from pycparser import c_ast
from pycparser.c_ast import NodeVisitor, UnaryOp, BinaryOp
from pycparser.c_generator import CGenerator

stackprinter.set_excepthook(style='darkbg2')

import subprocess
import argparse
import yaml


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


def find(pred, seq):
    for tl in seq:
        if pred(tl): return tl
    return None


class ExprCapture(pycparser.c_ast.NodeVisitor):
    def __init__(self):
        self.exprs = set()

    def generic_visit(self, node):
        NodeVisitor.generic_visit(self, node)

    def visit_BinaryOp(self, node: BinaryOp):
        self.exprs.add(node)
        NodeVisitor.generic_visit(self, node)

    def visit_UnaryOp(self, node: UnaryOp):
        self.exprs.add(node)
        NodeVisitor.generic_visit(self, node)

    def visit_FuncCall(self, node: UnaryOp):
        self.exprs.add(node)
        NodeVisitor.generic_visit(self, node)


class ContainsVariable(NodeVisitor):
    def __init__(self, variables: FrozenSet[str]):
        self.variables = variables
        self.found = False

    def visit_ID(self, node: c_ast.ID):
        if node.name in self.variables:
            self.found = True


def cycleCheck(node: c_ast.Node, parents=None):
    if not parents:
        parents = []

    parents.append(node)

    for c in node:
        if c in parents:
            raise BaseException("CYCLE!")
        cycleCheck(c, parents)
    parents.remove(node)


class ExtractFacts(object):
    def __init__(self, config, filename):
        self.config = config
        self.filename = filename
        self.tmpfile = "lohnsteuer_runtmp.c"
        self.executable = "lohnsteuer_run.out"
        self.prepare_command = "gcc -o %s %s" % (self.executable, self.tmpfile)
        self.run_command = "./" + self.executable

    def run(self):
        ast = pycparser.parse_file(self.filename, True, cpp_args="-DNOHEADER=1")
        symex = SymbolicExecution(ast)
        pp = CGenerator()
        keys = sorted(symex.defines.keys())
        for var in keys:
            value = symex.defines[var]
            print(f"{var} = ", pp.visit(value))
            # ast.show(showcoord=True)

        exprc = ExprCapture()
        for var, cvar, in symex.state.items():
            # cycleCheck(expr)
            # exprc.visit(expr)
            pass  # print(len(exprc.exprs))

        # cap = ExprCapture()
        # cap.visit(ast)
        # print(cap.exprs)


class ExecutePipeline(object):
    def __init__(self, config, filename):
        self.config = config
        self.filename = filename
        self.tmpfile = "lohnsteuer_runtmp.c"
        self.executable = "lohnsteuer_run.out"
        self.prepare_command = "gcc -o %s %s" % (self.executable, self.tmpfile)
        self.run_command = "./" + self.executable

    def run(self):
        self.inject()
        self.compile()
        self.execute()

    def compile(self):
        print("Compile generated c file: ", self.prepare_command)
        errorlevel = os.system(self.prepare_command)
        if errorlevel > 0:
            sys.exit(errorlevel)

    def execute(self):
        print("Compile generated c file: ", self.run_command)
        output = subprocess.check_output(self.run_command).decode()
        print(output)
        output = yaml.safe_load(output)
        self.config['OUTPUTS'] = output['OUTPUTS']

    def inject(self):
        with open(self.filename) as fh:
            text = fh.read()

        assignments = ""
        for (name, value) in self.config['INPUTS'].items():
            assignments += f"\n{name} = {value};"

        outputs = '\nprintf("\\nOUTPUTS:\\n");'
        for name in self.config['OUTPUTS'].keys():
            outputs += f'\nprintf("  - {name}: %f\\n", {name});'

        text = text.replace('//%INPUT%', assignments) \
            .replace('//%OUTPUT%', outputs) \
            .replace('//%HEADER%', '#include <stdio.h>')

        with open(self.tmpfile, 'w') as fh:
            fh.write(text)


class CBMCPipeline(object):
    def __init__(self, config, filename):
        self.config = config
        self.filename = filename
        self.tmpfile = "lohnsteuer_cbmctmp.c"
        self.smt_file = "lohnsteuer_cbmc.smt2"
        self.run_command = "z3 -smt2 " + self.smt_file
        self.prepare_command = f"cbmc --z3 --outfile {self.smt_file} {self.tmpfile}"

    def run(self):
        self.inject()
        self.generate_smt()
        # self.execute()

    def inject(self):
        with open(self.filename) as fh:
            text = fh.read()

        assignments = ""
        for (idx, value) in enumerate(self.config['FACTS']):
            assignments += f"\n__CPROVER_bool FACT_{idx};// = nondet_bool();"
            assignments += f"\n__CPROVER_input(\"FACT_{idx}\", FACT_{idx});"
            assignments += f"\nif(FACT_{idx}) __CPROVER_assume({value});"

        outputs = ""
        for (name, value) in self.config['OUTPUTS'].items():
            outputs += f'\n__CPROVER_assert({name} == {value}, "");'

        text = text.replace('//%INPUT%', assignments) \
            .replace('//%OUTPUT%', outputs)

        with open(self.tmpfile, 'w') as fh:
            fh.write(text)

    def generate_smt(self):
        print("Generate SMT file: ", self.prepare_command)
        errorlevel = os.system(self.prepare_command)
        if errorlevel > 0:
            sys.exit(errorlevel)

        with open(self.smt_file) as fh:
            smt2 = fh.read()

        search = re.compile(r'\(assert \(= \|main::1::FACT_(\d+)!0@1#1\| \|symex::io::(\d+)\|\)\)')
        new = r"(assert (! (= |main::1::FACT_\1!0@1#1| |symex::io::\2|) :named FACT_\1))"
        smt2 = search.sub(new, smt2)

        with open(self.smt_file, 'w') as fh:
            fh.write(smt2)

    def execute(self):
        print("Run SMT2 solver: ", self.run_command)
        output = subprocess.check_output(self.run_command).decode()
        print(output)
        output = yaml.safe_load(output)
        self.config['OUTPUTS'] = output['OUTPUTS']


class RenameingPrinter(CGenerator):
    def __init__(self, name_prefix: str):
        super().__init__(True)
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
            print("ERROR")

        new = c_ast.Decl(n.name + self.suffix,
                         n.quals, n.align, n.storage, n.funcspec, nt,
                         n.init, n.bitsize, n.coord)

        return super().visit_Decl(new, no_type)


class CBMCSelfCompPipeline(object):
    def __init__(self, config, args, filename):
        self.args = args
        self.config = config
        self.filename = filename
        self.tmpfile = "lohnsteuer_cbmcsc.c"
        self.smt_file = "lohnsteuer_cbmc.smt2"
        self.run_command = "cbmc " + self.tmpfile

    def run(self):
        self.inject()
        self.execute()

    def inject(self):
        ast = pycparser.parse_file(self.filename, True, cpp_args="-DNOHEADER=1")

        # known_variables = set(self.config['INPUTS'].keys())
        # to_1 = {v: f"{v}_1" for v in known_variables}
        # to_2 = {v: f"{v}_1" for v in known_variables}
        regex = re.compile(r'\b([A-Z]+)\b')

        def rename(prefix: str, text: str):
            return regex.sub(r'\1' + prefix, text)

        with open(self.tmpfile, 'w') as fh:
            fh.write(RenameingPrinter("_1").visit(ast))
            fh.write(RenameingPrinter("_2").visit(ast))
            fh.write("void main() {\n")

            for value in self.config['INPUTS'].keys():
                fh.write(f"\n{value}_1 = nondet_double();")
                fh.write(f"\n{value}_2 = nondet_double();")

            for (idx, value) in enumerate(self.config['FACTS']):
                fh.write(f"\n    // FACT {idx}")
                fh.write(f"\n    __CPROVER_assume(({rename('_1', value)}) == ({rename('_2', value)}));")

            if self.args.eqin:
                for value in self.config['INPUTS'].keys():
                    fh.write(f"\n    __CPROVER_assume({value}_1 == {value}_2);")
                for value in self.config['INTERNALS'].keys():
                    fh.write(f"\n    __CPROVER_assume({value}_1 == {value}_2);")

            main_fn: c_ast.FuncDef = find(lambda x: isinstance(x, c_ast.FuncDef) and x.decl.name == "main", ast.ext)
            body = main_fn.body.block_items
            for idx, statement in enumerate(body):
                fh.write(RenameingPrinter("_1").visit(statement))
                fh.write(";\n")
                fh.write(RenameingPrinter("_2").visit(statement))
                fh.write(";\n")
                for name in self.config['OUTPUTS'].keys():
                    fh.write(f"\n    __CPROVER_assert({name}_1 == {name}_2, \"Output {name} mismatch after {idx}\");")

            # fh.write("    main_1(); main_2();\n")

            fh.write("\n}")

        print(f"Run clang-format -i {self.tmpfile}")
        os.system(f"clang-format -i {self.tmpfile}")

    def execute(self):
        print("Run CBMC solver: ", self.run_command)
        #output = os.system(self.run_command)
        #sys.exit(output)


def get_cli():
    a = argparse.ArgumentParser()
    a.add_argument("--mode")
    a.add_argument("--eqin", default=True)
    a.add_argument("config")
    a.add_argument("program")
    return a


if __name__ == "__main__":
    ap = get_cli()
    args = ap.parse_args()

    with open(args.config) as fh:
        config = yaml.safe_load(fh)

    if args.mode == 'cbmc':
        pipeline = CBMCPipeline(config, args.program)
    elif args.mode == 'facts':
        pipeline = ExtractFacts(config, args.program)
    elif args.mode == 'selfcomp':
        pipeline = CBMCSelfCompPipeline(config, args, args.program)
    else:
        pipeline = ExecutePipeline(config, args.program)

    pipeline.run()
    with open(args.config, 'w') as fh:
        yaml.safe_dump(config, fh)
