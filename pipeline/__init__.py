import json
import os
import re
import subprocess
from collections import defaultdict
from pathlib import Path

import click
import pycparser
import yaml

from pipeline.evaluator import Evaluator
from pipeline.helper import *

TMP_FOLDER: Path = Path("./tmp").absolute()
ALTERNATIVE_YAML_OUT_FILENAME: Path = None
Z3 = "z3"
CBMC = "cbmc"


def group_options(*options):
    def wrapper(function):
        for option in reversed(options):
            function = option(function)
        return function

    return wrapper


ARG_CONFIG = click.argument("config", type=PPath(exists=True))
ARG_FILENAME = click.argument("filename", type=PPath(exists=True))
OPT_FACT_NAMES = click.option("-f", "--fact-names",
                              help="Sets the key in the YAML of the facts to be used. " + \
                                   "Typical you want USER_FACTS, AUTO_FACTS, or FACTS. " + \
                                   "Multiple keys are allowed",
                              multiple=True, default=['USER_FACTS'])


def log(*args):
    print(">>>", *args)


@click.group()
@click.option('--debug/--no-debug', default=False)
@click.option("-o", "--yaml-out", help="write updated config to a different file", metavar="FILE", type=click.Path())
@click.option("--no-meta-update", help="disables the output of the meta-file", default=False, is_flag=True)
@click.option("--tmp", help="Folder for temporary files", metavar="FOLDER", default=Path("./tmp"), type=click.Path())
@click.option("--cbmc", help="Command/Path to execute CBMC. Settable via env. variable $CBMC", envvar="CBMC",
              default="cbmc")
@click.option("--z3", help="Command/Path to execute Z3. Settable via env. variable Z3", envvar="Z3",
              default="z3")
def cli(debug, tmp, yaml_out, cbmc, z3, no_meta_update):
    global TMP_FOLDER, ALTERNATIVE_YAML_OUT_FILENAME, Z3, CBMC
    TMP_FOLDER = tmp.absolute()
    TMP_FOLDER.mkdir(exist_ok=True)

    if yaml_out:
        ALTERNATIVE_YAML_OUT_FILENAME = yaml_out

    if cbmc: CBMC = cbmc
    if z3: Z3 = z3


def _load_config(fn):
    with open(fn) as fh:
        return yaml.safe_load(fh)


def _save_config(filename, value):
    global ALTERNATIVE_YAML_OUT_FILENAME
    if ALTERNATIVE_YAML_OUT_FILENAME:
        target = ALTERNATIVE_YAML_OUT_FILENAME
    else:
        target = filename
    with open(target, 'w') as fh:
        yaml.safe_dump(value, fh)


class auto_save_config:
    def __init__(self, fn: Path):
        self.fn = fn
        self.config = None

    def __enter__(self):
        self.config = _load_config(self.fn)
        return self.config

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_val is None: _save_config(self.fn, self.config)


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME)
@click.option("-f", "--fact-name", default="AUTO_FACTS")
def extract_facts_fwd(config, filename, fact_name):
    """Extracts facts by symbolical and concrete execution (fwd-calculi)."""

    with auto_save_config(config) as config:
        ast: c_ast.FileAST = pycparser.parse_file(filename, True,
                                                  cpp_args="-DNOHEADER=1")
        e = Evaluator(ast, config)
        out = CGenerator()
        local_facts = []
        for s in e.computation_trace:
            if isinstance(s, c_ast.FuncCall):
                txt = out.visit(s.args)
                local_facts.append(txt.replace("False","false").replace('True','true'))

        trace_computation = list(e.computation_trace)
        for tc in trace_computation:
            log(out.visit(tc))

        trace_computation.reverse()
        for var in config['OUTPUTS'].keys():
            log(f"Output constraint {var}")
            last_assign: Assignment = find(
                lambda x: x is not None and isinstance(x, Assignment) and x.lvalue.name == var,
                trace_computation)
            value = e.memory[var]
            log(f"Value of {var}: {value}")
            if last_assign:
                expr = last_assign.rvalue
                svalue = e.expr_rewriter.visit(expr)
                log(f"Symbolic value of {var}: {svalue}")
                if not isinstance(svalue, c_ast.Node):
                    if svalue == value: continue
                    svalue = Constant('int', svalue)
                if svalue != value:
                    eq = BinaryOp("==", svalue, Constant('int', value))
                    local_facts.append(out.visit(eq))
            else:
                log(f"No assigment found for {var} in computation trace")

        config[fact_name] = local_facts


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME)
def extract_facts(config, filename):
    expressions = []
    ast: c_ast.FileAST
    config = config
    filename = filename
    tmpfile = "lohnsteuer_runtmp.c"
    executable = "lohnsteuer_run.out"
    prepare_command = "gcc -o %s %s" % (executable, tmpfile)
    run_command = "./" + executable
    facts = list()

    def input_equalities():
        for (k, v) in config["INPUTS"].items():
            facts.append(f"{k}=={v}")
            facts.append(f"{k}<={v}")
            facts.append(f"{k}>={v}")

    def simple_binary_comparison_in_source():
        nonlocal facts

        def simple_binary(node: c_ast.Node):
            if isinstance(node, c_ast.BinaryOp):
                (l, r) = (node.left, node.right)
                if isinstance(l, c_ast.Constant):
                    (const, var) = (l, r)
                elif isinstance(r, c_ast.Constant):
                    (const, var) = (r, l)
                else:
                    return None

                if isinstance(var, c_ast.ID) and var.name in config['INPUTS']:
                    return CGenerator().visit(node)
            return None

        pred = lambda x: input_pure(x, config['INPUTS'])
        facts += filter(lambda x: x is not None, map(pred, expressions))

    def equality_heuristics():
        pass

    def symbex():
        revar = re.compile(r"\b[a-zA-Z_][_a-zA-Z0-9]*\b")
        reconst = re.compile(r"\b\d+\b")

        def extract_cv(expr: str, lhs: str):
            vars = [lhs] + revar.findall(expr)
            vars = map(lambda x: x if '_' not in x else x[0:x.find('_')], vars)
            return frozenset(vars), frozenset(reconst.findall(expr))

        p = EmbeddingPrinter(2, symex)
        pairs = set()
        facts = set()

        for var, cvar in symex.state.items():
            if cvar in symex.defines:
                s = p.visit(symex.defines[cvar])
                pairs.add(extract_cv(s, var))

        for (vars, consts) in pairs:
            for v in vars:
                if v not in config['INPUTS']:
                    continue
                for c in consts:
                    facts.add(f"{v} == {c}")
                    facts.add(f"{v} < {c}")
                    facts.add(f"{v} > {c}")

        facts += facts

    with auto_save_config(config) as config:
        ast = pycparser.parse_file(filename, True, cpp_args="-DNOHEADER=1")
        capture = ExprCapture()
        capture.visit(ast)
        expressions = capture.exprs
        # constants = capture.constants
        symex = SymbolicExecution(ast)

        input_equalities()
        simple_binary_comparison_in_source()
        equality_heuristics()
        symbex()
        config['AUTO_FACTS'] = facts


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME)
@click.option("--store-output", default=True, is_flag=True)
def execute(config, filename: Path, store_output):
    """
    Executes the given program by compiling  and injecting the concrete values givne in the meta-file.

    :param config: the YAML meta-file
    :param filename: path to C-program
    :param store_output:  set to True if the output should be stored in the meta-file
    """
    print(type(filename))
    tmpfile = TMP_FOLDER / (filename.stem + "_run.c")
    executable = TMP_FOLDER / (filename.stem + "_run")
    prepare_command = "gcc -o %s %s" % (executable, tmpfile)
    run_command = executable

    cfg = _load_config(config)

    def _inject():
        log("Inject input assignments")
        assignments = ""
        for (name, value) in cfg['INPUTS'].items():
            assignments += f"\n{name} = {value};"

        outputs = '\nprintf("\\nOUTPUTS:\\n");'
        for name in cfg['OUTPUTS'].keys():
            outputs += f'\nprintf("  {name}: %d\\n", {name});'

        _augment_program(filename, tmpfile, assignments, outputs, '#include <stdio.h>')

    def _compile():
        log("Compile generated C file:", prepare_command)
        error_level = os.system(prepare_command)
        if error_level > 0:
            sys.exit(error_level)

    def _execute():
        log("Run executable:", run_command)
        output = subprocess.check_output(run_command).decode()
        log(output)
        if store_output:
            log("Update output assignments in the given YAML file")
            output = yaml.safe_load(output)
            cfg['OUTPUTS'] = output['OUTPUTS']
            _save_config(config, cfg)

    _inject()
    _compile()
    _execute()


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME, OPT_FACT_NAMES)
def fact_consistency(config: Path, filename: Path, fact_names: typing.List[str]):
    """
    Checks the consistency (abscence of contradiction) facts
    on the given facts.
    """
    log("Using given fact keys:", fact_names)

    tmp_file = TMP_FOLDER / (filename.stem + "_cbmc_contracheck.c")
    config = _load_config(config)

    a = ""
    for var in config['INPUTS']:
        a += f"\n{var}=nondet_int();"

    for (idx, value) in enumerate(_get_facts(config, fact_names)):
        log(f"> Add fact {value}")
        a += f"\n__CPROVER_assume({value});"
    _augment_program(filename, tmp_file, assume=a + "assert(false);return 0;")

    run_command = f"cbmc {tmp_file}"
    exitcode, _ = subprocess.getstatusoutput(run_command)
    if exitcode != 0:
        log(f"Successful: Facts are consistent {exitcode}==0")
        return True
    else:
        log(f"Error: Facts are inconsistent {exitcode}==0")
        sys.exit(1)
        # return False


def cbmc_args(config):
    if 'CBMC' in config:
        return ' '.join(f"--{k} {v}" for k,v in config['CBMC'].items())
    return ""


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME, OPT_FACT_NAMES)
def facts_preciseness(config, filename, fact_names):
    """Checks the preciseness of the given facts
    to achieve the desired outcome.
    """

    tmp_file = TMP_FOLDER / (filename.stem + "_cbmc_preciseness_check.c")
    config = _load_config(config)

    a = ""
    b = ""

    a = ""
    for var in config['INPUTS']:
        a += f"\n{var}=nondet_int();"

    for (idx, value) in enumerate(_get_facts(config, fact_names)):
        log(f"> Add fact {value}")
        a += f"\n__CPROVER_assume({value});"

    for (out, value) in config['OUTPUTS'].items():
        log(f"> Add assertion {out} == {value}")
        b += f"\n__CPROVER_assert({out}=={value}, \"Output {out}\");"

    _augment_program(filename, tmp_file, a, b)

    run_command = f"cbmc {cbmc_args(config)} {tmp_file}"
    log(f"Execute {run_command}")
    exitcode, output = subprocess.getstatusoutput(run_command)
    print(output)
    if exitcode == 0:
        log(f"Successful: Facts are precise {exitcode}==0")
        return True
    else:
        log(f"Error: Facts are imprecise {exitcode==0}")
        sys.exit(1)
        # return False


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME, OPT_FACT_NAMES)
def fact_incompatibility(config: Path, filename: Path, fact_names: typing.List[str]):
    tmp_file = TMP_FOLDER / (filename.stem + "_cbmc_contracheck.smt2")
    program = """"""

    config = _load_config(config)

    for n in config['INPUTS'].keys():
        program += f"(declare-const {n} Int);\n"

    regex = re.compile(r"(.*) (==|<=|>|<|>=|!=) (.*)")

    def postfix(s):
        return regex.sub(r'(\2 \1 \3)', s)

    F = _get_facts(config, fact_names)
    facts = list(map(postfix, F))

    for f1 in facts:
        for f2 in facts:
            program += "\n\n(push 1)"
            program += f"\n(assert (and {f1} {f2}))"
            program += "\n(check-sat)"
            program += "\n(pop 1)"

    tmp_file.write_text(program)
    log("Write ", tmp_file)
    log("Call ", f"z3 -smt2 {tmp_file}")
    ecode, out = subprocess.getstatusoutput(f"z3 -smt2 {tmp_file}")
    contra_table = defaultdict(list)
    L = len(F)
    for idx, line in enumerate(out.splitlines(False)):
        if line == 'unsat':
            f1 = F[int(idx / L)]
            f2 = F[idx % L]
            log(f"Conflict between {f1} and {f2}")
            contra_table[f1].append(f2)

    config['XOR_FACTS'] = dict(contra_table)

    # def run_maxsat(self):
    #     program = ""
    #     for n in config['INPUTS'].keys():
    #         program += f"(declare-const {n} Int);\n"
    #
    #     regex = re.compile(r"(.*) (==|<=|>|<|>=|!=) (.*)")
    #
    #     def postfix(s):
    #         return regex.sub(r'(\2 \1 \3)', s)
    #
    #     F = config['AUTO_FACTS'] + config['USER_FACTS']
    #     facts = list(map(postfix, F))
    #
    #     for idx, f1 in enumerate(facts):
    #         program += f"\n(declare-const F{idx} Bool)"
    #         program += f"\n(assert-soft F{idx} :weight 1)"
    #         program += f"\n(assert (or (not F{idx}) {f1}))"
    #     program += "\n(check-sat) (get-model)"
    #
    #     tmp_file.write_text(program)
    #     log("Write ", tmp_file)
    #     log("Call ", f"z3 -smt2 {tmp_file}")
    #     ecode, out = subprocess.getstatusoutput(f"z3 -smt2 {tmp_file}")


def _augment_program(in_file: Path, out_file: Path, assume="", output="", header=""):
    text = in_file.read_text()
    text = text.replace('//%INPUT%', assume) \
        .replace('//%OUTPUT%', output) \
        .replace('//%HEADER%', header)
    out_file.write_text(text)


def _get_facts(config: dict, fact_names: typing.List[str]):
    facts = []
    for k in fact_names:
        facts += config[k]
    return facts


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME, OPT_FACT_NAMES)
@click.option("-s", "--set-output-values", default=False, is_flag=True)
def symbex(config, filename: Path, fact_names: typing.List[str], set_output_values):
    """
    Compute outcome based on a set of facts. Determine the outcome of the given program under the given symbolic facts.
    Uses CBMC to generate a counter-example.

    FILENAME is the path to an augmentable C-program, and CONFIG points to YAML file containing the meta-data.
    """
    cfg = _load_config(config)
    filename = filename
    tmpfile = TMP_FOLDER / (filename.stem + "_cbmc_symbex.c")
    run_command = f"cbmc --json-ui --trace {tmpfile}"

    assignments = ""
    outputs = ""

    for var in cfg['INPUTS']:
        assignments += f"\n{var} = nondet_int();"

    log(f"Use facts: {fact_names}")
    for (idx, value) in enumerate(_get_facts(cfg, fact_names)):
        log(f"> Add fact {value}")
        assignments += f"\n__CPROVER_assume({value});"

    outputs += f'\n__CPROVER_assert(0==1, "");'

    _augment_program(filename, tmpfile, assignments, outputs)

    log("Run CBMC:", run_command)
    exitcode, output = subprocess.getstatusoutput(run_command)
    jout = json.loads(output)

    for entry in jout:
        if "result" in entry:
            result = entry['result'][0]['trace']
            result.reverse()
            for out in cfg['OUTPUTS'].keys():
                val = find(lambda x:
                           'assignmentType' in x \
                           and x["assignmentType"] == "variable" \
                           and x['lhs'] == out, result)
                if val:
                    v = int(val['value']['binary'], 2)
                    print(f"{out} = {v}")
                    if set_output_values:
                        cfg['OUTPUTS'][out] = v
                else:
                    print(f"{out} = {val}")

    if set_output_values:
        _save_config(config, cfg)


@cli.command()
@group_options(ARG_CONFIG, ARG_FILENAME, OPT_FACT_NAMES)
def minimize_facts_core(config, filename: Path, fact_names):
    tmpfile = TMP_FOLDER / (filename.stem + "_cbmc_factmcheck.c")
    smt_file = TMP_FOLDER / (filename.stem + "_cbmc_factmcheck.smt2")
    cfg = _load_config(config)
    prepare_command = f"cbmc {cbmc_args(cfg)} --z3 --outfile {smt_file} {tmpfile}"
    facts = _get_facts(cfg, fact_names)
    # facts = filter_facts(facts)  # only satisfied facts are allowed

    def _inject():
        # respect_contra_table = 'XOR_FACTS' in config and \
        #                       len(config['XOR_FACTS']) > 0 and \
        #                       not ignore_xor_facts

        log("Inject fact as assumption")

        assignments = ""
        for var in cfg['INPUTS']:
            assignments += f"\n{var} = nondet_int();"

        for (idx, value) in enumerate(facts):
            log(f"> Add fact {value}")
            assignments += f"\n__CPROVER_bool FACT_{idx}; //FACT_{idx} = 1;"
            assignments += f"\nif(FACT_{idx}) __CPROVER_assume({value});"

        # if respect_contra_table and False:
        #    log("Prevent selection of contradictory facts!")
        #    xor_facts = config['XOR_FACTS']
        #    for (idx, value) in enumerate(facts):
        #        if value in xor_facts:
        #            log(f"> Contraction for {value} : {xor_facts[value]}")
        #            for xf in xor_facts[value]:
        #                xidx = facts.index(xf)
        #                assignments += f"\n__CPROVER_assume( !FACT_{idx} || !FACT_{xidx});"
        #        else:
        #            log(f"> No contraction known for {value}")

        log(f"Inject output as assertions")
        outputs = ""
        for (name, value) in cfg['OUTPUTS'].items():
            log(f"> Add output {name} == {value}")
            outputs += f'\n__CPROVER_assert({name} == {value}, "Output: {name}");'

        _augment_program(filename, tmpfile, assignments, outputs)

    def _generate_smt():
        log("Generate SMT file: ", prepare_command)
        errorlevel = os.system(prepare_command)
        if errorlevel > 0:
            sys.exit(errorlevel)

        smt2 = smt_file.read_text()

        # search = re.compile(r'\(assert \(= \|main::1::FACT_(\d+)!0@1#1\| \|symex::io::(\d+)\|\)\)')
        # new = r"(assert (! (= |main::1::FACT_\1!0@1#1| |symex::io::\2|) :named FACT_\1))"
        # search.sub(new, smt2)

        named = ""
        for idx, value in enumerate(facts):
            named += f"\n(assert (! (= |main::1::FACT_{idx}!0@1#1| true) :named FACT_{idx}))"
        smt2 = smt2.replace("(check-sat)", named + "\n(check-sat)\n(get-unsat-core)")

        log("Inject names and options into SMT file.")
        with open(smt_file, 'w') as fh:
            fh.write(";; Force z3 to compute the minimal unsat-core\n"
                     "(set-option :produce-unsat-cores true)\n"
                     "(set-option :smt.core.minimize true)\n")
            fh.write(smt2)

    def _execute():
        cmd = f"z3 -smt2 {smt_file}"
        log("Run SMT2 solver: ", cmd)
        exitcode, output = subprocess.getstatusoutput(cmd)
        lines = output.split("\n")
        if lines[0] == "unsat":
            unsat_core = lines[1].strip("()").split(" ")
            log("Required facts: ", unsat_core)
            selected_fact_ids = [int(x[len('FACT_'):]) for x in unsat_core]
            selected_facts = [facts[i] for i in selected_fact_ids]
            log("Selected facts", selected_facts)
            cfg['SELECTED_FACTS'] = selected_facts
            _save_config(config, cfg)
        else:
            log("Given set of facts are insufficient to guarantee the output.")
            sys.exit(2)

    _inject()
    _generate_smt()
    _execute()


def call_z3(smt_file):
    log("Call ", f"z3 -smt2 {smt_file}")
    ecode, out = subprocess.getstatusoutput(f"z3 -smt2 {smt_file}")
    log(f"SMT result $?={ecode}")
    return out


REGEX_C2SMT = re.compile(r"(.*) (==|<=|>|<|>=|!=) (.*)")


def c2smt(expr: str) -> str:
    return REGEX_C2SMT.sub(r'(\2 \1 \3)', expr)


def filter_facts(config, facts):
    inputs = config['INPUTS']
    smt_problem = ""
    for n, v in inputs.items():
        smt_problem += f"(define-const {n} Int {v});\n"

    for f1 in facts:
        smt_problem += "\n(push)"
        smt_problem += f"\n(assert {c2smt(f1)})"
        smt_problem += "\n(check-sat)"
        smt_problem += "\n(pop)"

    contra_tmp_file = TMP_FOLDER / "filter_facts.smt2"
    contra_tmp_file.write_text(smt_problem)
    log("Write ", contra_tmp_file)
    out = [idx for idx, x in enumerate(call_z3(contra_tmp_file).splitlines())
           if x == 'sat']
    print(out)
    valid_facts = list(map(lambda x: facts[x], out))
    log("Valid facts are: ")
    for f in valid_facts:
        log("  * ", f)
    return valid_facts


@cli.command()
@click.option("--eqin", help="", default=True, type=click.BOOL)
def unique_selfcomp(config, filename, eqin=True):
    """
    Checks the uniqueness of the facts using self-composition.

    :param config:
    :param filename:
    :param eqin:
    :return:
    """
    tmpfile = "lohnsteuer_cbmcsc.c"
    smt_file = "lohnsteuer_cbmc.smt2"
    run_command = f"cbmc {cbmc_args(config)} --z3 --trace {tmpfile}"

    ast = pycparser.parse_file(filename, True, cpp_args="-DNOHEADER=1")

    # known_variables = set(config['INPUTS'].keys())
    # to_1 = {v: f"{v}_1" for v in known_variables}
    # to_2 = {v: f"{v}_1" for v in known_variables}
    regex = re.compile(r'\b([A-Z]+)\b')

    def rename(prefix: str, text: str):
        return regex.sub(r'\1' + prefix, text)

    with open(tmpfile, 'w') as fh:
        fh.write(RenameingPrinter("_1").visit(ast))
        fh.write(RenameingPrinter("_2").visit(ast))
        fh.write("void main() {\n")

        for value in config['INPUTS'].keys():
            fh.write(f"\n{value}_1 = nondet_double();")
            fh.write(f"\n{value}_2 = nondet_double();")

        for (idx, value) in enumerate(config['USER_FACTS'] + config['AUTO_FACTS']):
            fh.write(f"\n    // FACT {idx}")
            fh.write(f"\n    __CPROVER_assume(({rename('_1', value)}) == ({rename('_2', value)}));")

        if eqin:
            for value in config['INPUTS'].keys():
                fh.write(f"\n    __CPROVER_assume({value}_1 == {value}_2);")
            for value in config['INTERNALS'].keys():
                fh.write(f"\n    __CPROVER_assume({value}_1 == {value}_2);")

        main_fn: c_ast.FuncDef = find(lambda x: isinstance(x, c_ast.FuncDef) and x.decl.name == "main", ast.ext)
        body = main_fn.body.block_items
        for idx, statement in enumerate(body):
            fh.write(RenameingPrinter("_1").visit(statement))
            fh.write(";\n")
            fh.write(RenameingPrinter("_2").visit(statement))
            fh.write(";\n")
            for name in config['OUTPUTS'].keys():
                fh.write(f"\n    __CPROVER_assert({name}_1 == {name}_2, \"Output {name} mismatch after {idx}\");")

            if eqin:
                for value in config['INPUTS'].keys():
                    fh.write(f"\n    __CPROVER_assert({value}_1 == {value}_2, \"\");")
                for value in config['INTERNALS'].keys():
                    fh.write(f"\n    __CPROVER_assert({value}_1 == {value}_2, \"\");")

        fh.write("\n}")

    log(f"Run clang-format -i {tmpfile}")
    os.system(f"clang-format -i {tmpfile}")

    log("Run CBMC solver: ", run_command)
    sys.exit(os.system(run_command))


cli.add_command(extract_facts_fwd)


def main():
    cli()

#
# def main0():
#     ap = get_cli()
#     args = ap.parse_args()
#
#     program = Path(args.program)
#
#     TMP_FOLDER = Path(args.tmp).absolute()
#     TMP_FOLDER.mkdir(exist_ok=True)
#
#     with open(args.config) as fh:
#         config = yaml.safe_load(fh)

# if args.mode == 'cbmc':
#    pipeline = CBMCFactsMinimalism(config, program)
# elif args.mode == 'facts':
#    pipeline = ExtractFacts(config, program)
# elif args.mode == 'rfacts':
#    pipeline = extract_facts_fwd(config, program)
# elif args.mode == 'selfcomp':
#       pipeline = CBMCFactUniqueness(config, args, program)
# elif args.mode == 'check':
#    pipeline = CBMCFactsMinimalism(config, args, program)
# elif args.mode == 'run':
#    pipeline = ExecutePipeline(config, program)
# elif args.mode == 'check_contra':
#    pipeline = CheckForContradiction(config, program)
# else:
#    log(f"Unknown mode {args.mode} given.")
#    sys.exit(1)

# pipeline.run()
#
# with open(args.config if args.o is None else args.o, 'w') as fh:
#     yaml.safe_dump(config, fh)
