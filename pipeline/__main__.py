#!/usr/bin/python
import os
import re
from .helper import *
from pathlib import Path
import typing

import pycparser

from pycparser import c_ast
from pycparser.c_generator import CGenerator

import subprocess
import argparse
import yaml

TMP_FOLDER: Path = Path("./tmp").absolute()


def log(*args):
    print(">>>", *args)


class ExtractFacts(object):
    def __init__(self, config, filename):
        self.expressions = []
        self.ast: c_ast.FileAST
        self.config = config
        self.filename = filename
        self.tmpfile = "lohnsteuer_runtmp.c"
        self.executable = "lohnsteuer_run.out"
        self.prepare_command = "gcc -o %s %s" % (self.executable, self.tmpfile)
        self.run_command = "./" + self.executable

        self.facts = list()

    def input_equalities(self):
        for (k, v) in self.config["INPUTS"].items():
            self.facts.append(f"{k}=={v}")
            self.facts.append(f"{k}<={v}")
            self.facts.append(f"{k}>={v}")

    def run(self):
        self.ast = pycparser.parse_file(self.filename, True, cpp_args="-DNOHEADER=1")
        capture = ExprCapture()
        capture.visit(self.ast)
        self.expressions = capture.exprs
        # self.constants = capture.constants
        self.symex = SymbolicExecution(self.ast)

        self.input_equalities()
        self.simple_binary_comparison_in_source()
        self.equality_heuristics()
        self.symbex()

        # import pprint
        # pprint.pprint(self.facts)
        self.config['AUTO_FACTS'] = self.facts

    def simple_binary_comparison_in_source(self):
        def simple_binary(node: c_ast.Node):
            if isinstance(node, c_ast.BinaryOp):
                (l, r) = (node.left, node.right)
                if isinstance(l, c_ast.Constant):
                    (const, var) = (l, r)
                elif isinstance(r, c_ast.Constant):
                    (const, var) = (r, l)
                else:
                    return None

                if isinstance(var, c_ast.ID) and var.name in self.config['INPUTS']:
                    return CGenerator().visit(node)
            return None

        pred = lambda x: input_pure(x, self.config['INPUTS'])
        self.facts += filter(lambda x: x is not None, map(pred, self.expressions))

    def equality_heuristics(self):
        pass

    def symbex(self):
        revar = re.compile(r"\b[a-zA-Z_][_a-zA-Z0-9]*\b")
        reconst = re.compile(r"\b\d+\b")

        def extract_cv(expr: str, lhs: str):
            vars = [lhs] + revar.findall(expr)
            vars = map(lambda x: x if '_' not in x else x[0:x.find('_')], vars)
            return frozenset(vars), frozenset(reconst.findall(expr))

        p = EmbeddingPrinter(2, self.symex)
        pairs = set()
        facts = set()

        for var, cvar in self.symex.state.items():
            if cvar in self.symex.defines:
                s = p.visit(self.symex.defines[cvar])
                pairs.add(extract_cv(s, var))

        for (vars, consts) in pairs:
            for v in vars:
                if v not in self.config['INPUTS']:
                    continue
                for c in consts:
                    facts.add(f"{v} == {c}")
                    facts.add(f"{v} < {c}")
                    facts.add(f"{v} > {c}")

        self.facts += facts


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


class ExecutePipeline(object):
    def __init__(self, config, filename: Path):
        self.config = config
        self.filename = filename
        self.tmpfile = TMP_FOLDER / (filename.stem + "_run.c")
        self.executable = TMP_FOLDER / (filename.stem + "_run")
        self.prepare_command = "gcc -o %s %s" % (self.executable, self.tmpfile)
        self.run_command = self.executable

    def run(self):
        self._inject()
        self._compile()
        self._execute()

    def _inject(self):
        log("Inject input assignments")

        with open(self.filename) as fh:
            text = fh.read()

        assignments = ""
        for (name, value) in self.config['INPUTS'].items():
            assignments += f"\n{name} = {value};"

        outputs = '\nprintf("\\nOUTPUTS:\\n");'
        for name in self.config['OUTPUTS'].keys():
            outputs += f'\nprintf("  {name}: %d\\n", {name});'

        text = text.replace('//%INPUT%', assignments) \
            .replace('//%OUTPUT%', outputs) \
            .replace('//%HEADER%', '#include <stdio.h>')

        with open(self.tmpfile, 'w') as fh:
            fh.write(text)

    def _compile(self):
        log("Compile generated C file:", self.prepare_command)
        error_level = os.system(self.prepare_command)
        if error_level > 0:
            sys.exit(error_level)

    def _execute(self):
        log("Run executable:", self.run_command)
        output = subprocess.check_output(self.run_command).decode()
        log(output)
        log("Update output assignments in the given YAML file")
        output = yaml.safe_load(output)
        self.config['OUTPUTS'] = output['OUTPUTS']


class CheckForContradiction(object):
    def __init__(self, config, filename: Path):
        self.config = config
        self.filename = filename
        self.tmp_file = TMP_FOLDER / (filename.stem + "_cbmc_contracheck.c")

    def run(self):
        program = """
        int main() {
        """
        for n in self.config['INPUTS'].keys():
            program += f"int {n};\n"

        facts = self.config['AUTO_FACTS'] + self.config['USER_FACTS']
        for f1 in facts:
            for f2 in facts:
                program += f"assert(!(({f1}) && ({f2})));\n"

        program += "}"
        self.tmp_file.write_text(program)
        log("Write ", self.tmp_file)
        #ecode, out = subprocess.getstatusoutput(["z3", "-program", self.tmp_file])


class CBMCFactsMinimalism(object):
    def __init__(self, config, filename: Path):
        self.config = config
        self.filename = filename
        self.tmpfile = TMP_FOLDER / (filename.stem + "_cbmc_factmcheck.c")
        self.smt_file = TMP_FOLDER / (filename.stem + "_cbmc_factmcheck.smt2")
        self.prepare_command = f"cbmc --z3 --outfile {self.smt_file} {self.tmpfile}"

    def run(self):
        self._inject()
        self._generate_smt()
        self._execute()

    def _inject(self):
        log("Inject fact as assumption")
        text = self.filename.read_text()

        assignments = "__CPROVER_bool TRUE = 1; //A constant which is always true\n"
        for (idx, value) in enumerate(self.config['USER_FACTS'] + self.config['AUTO_FACTS']):
            log(f"> Add fact {value}")
            assignments += f"\n__CPROVER_bool FACT_{idx}; //FACT_{idx} = 1;"
            # assignments += f"\n__CPROVER_input(\"FACT_{idx}\", FACT_{idx});"
            assignments += f"\nif(FACT_{idx}) __CPROVER_assume({value});"

        log(f"Inject output as assertions")
        outputs = ""
        for (name, value) in self.config['OUTPUTS'].items():
            log(f"> Add output {name} == {value}")
            outputs += f'\n__CPROVER_assert({name} == {value}, "Output: {name}");'

        text = text.replace('//%INPUT%', assignments).replace('//%OUTPUT%', outputs)

        self.tmpfile.write_text(text)

    def _generate_smt(self):
        log("Generate SMT file: ", self.prepare_command)
        errorlevel = os.system(self.prepare_command)
        if errorlevel > 0:
            sys.exit(errorlevel)

        smt2 = self.smt_file.read_text()

        search = re.compile(r'\(assert \(= \|main::1::FACT_(\d+)!0@1#1\| \|symex::io::(\d+)\|\)\)')
        # new = r"(assert (! (= |main::1::FACT_\1!0@1#1| |symex::io::\2|) :named FACT_\1))"
        # search.sub(new, smt2)

        named = ""
        for idx, value in enumerate(self.config['USER_FACTS'] + self.config['AUTO_FACTS']):
            named += f"\n(assert (! (= |main::1::FACT_{idx}!0@1#1| true) :named FACT_{idx}))"
        smt2 = smt2.replace("(check-sat)", named + "\n(check-sat)\n(get-unsat-core)")

        log("Inject names and options into SMT file.")
        with open(self.smt_file, 'w') as fh:
            fh.write(";; Force z3 to compute the minimal unsat-core\n"
                     "(set-option :produce-unsat-cores true)\n"
                     "(set-option :smt.core.minimize true)\n")
            fh.write(smt2)

    def _execute(self):
        log("Run SMT2 solver: z3 -smt2 ", self.smt_file)
        exitcode, output = subprocess.getstatusoutput(f"z3 -smt2 {self.smt_file}")
        lines = output.split("\n")
        if lines[0] == "unsat":
            unsat_core = lines[1].strip("()").split(" ")
            log("Required facts: ", unsat_core)
            selected_fact_ids = [int(x[len('FACT_'):]) for x in unsat_core]
            facts = self.config['USER_FACTS'] + self.config['AUTO_FACTS']
            selected_facts = [facts[i] for i in selected_fact_ids]
            log("Selected facts", selected_facts)
            self.config['SELECTED_FACTS'] = selected_facts
        else:
            log("Given set of facts are insufficient to guarantee output.")
            sys.exit(2)


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
            log("ERROR")

        new = c_ast.Decl(n.name + self.suffix,
                         n.quals, n.align, n.storage, n.funcspec, nt,
                         n.init, n.bitsize, n.coord)

        return super().visit_Decl(new, no_type)


class CBMCFactUniqueness(object):
    def __init__(self, config, args, filename):
        self.args = args
        self.config = config
        self.filename = filename
        self.tmpfile = "lohnsteuer_cbmcsc.c"
        self.smt_file = "lohnsteuer_cbmc.smt2"
        self.run_command = "cbmc --z3 --trace" + self.tmpfile

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

            for (idx, value) in enumerate(self.config['USER_FACTS'] + self.config['AUTO_FACTS']):
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

                if self.args.eqin:
                    for value in self.config['INPUTS'].keys():
                        fh.write(f"\n    __CPROVER_assert({value}_1 == {value}_2, \"\");")
                    for value in self.config['INTERNALS'].keys():
                        fh.write(f"\n    __CPROVER_assert({value}_1 == {value}_2, \"\");")

            fh.write("\n}")

        log(f"Run clang-format -i {self.tmpfile}")
        os.system(f"clang-format -i {self.tmpfile}")

    def execute(self):
        log("Run CBMC solver: ", self.run_command)
        sys.exit(os.system(self.run_command))


def get_cli():
    a = argparse.ArgumentParser()
    a.add_argument("--mode", help="Operation mode")
    a.add_argument("--datatype", help="int or float", default="int")
    a.add_argument("--tmp", help="Folder for temporary files", metavar="FOLDER", default="tmp")
    a.add_argument("--eqin", help="", default=True)
    a.add_argument("config", help="meta data of the given program")
    a.add_argument("program", help="a C-program file")
    return a


# class ProgramConfig():
#    def __init__(self):
#        self.auto_facts: typing.List[str] = []
#        self.user_facts: typing.List[str] = []
#        self.inputs: typing.Dict[str, str] = {}
#        self.outputs: typing.Dict[str, str] = {}
#        self.internals: typing.Dict[str, str] = {}
#
#    def facts(self):
#        return self.auto_facts + self.user_facts


if __name__ == "__main__":
    ap = get_cli()
    args = ap.parse_args()

    program = Path(args.program)

    TMP_FOLDER = Path(args.tmp).absolute()
    TMP_FOLDER.mkdir(exist_ok=True)

    with open(args.config) as fh:
        config = yaml.safe_load(fh)

    if args.mode == 'cbmc':
        pipeline = CBMCFactsMinimalism(config, program)
    elif args.mode == 'facts':
        pipeline = ExtractFacts(config, program)
    elif args.mode == 'selfcomp':
        pipeline = CBMCFactUniqueness(config, args, program)
    elif args.mode == 'check':
        pipeline = CBMCFactsMinimalism(config, program)
    elif args.mode == 'run':
        pipeline = ExecutePipeline(config, program)
    elif args.mode == 'check_contra':
        pipeline = CheckForContradiction(config, program)
    else:
        log(f"Unknown mode {args.mode} given.")
        sys.exit(1)

    pipeline.run()
    with open(args.config, 'w') as fh:
        yaml.safe_dump(config, fh)
