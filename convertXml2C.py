import re
import arpeggio
import re

import arpeggio


def build_expr_parser():
    grammar = open("grammar.txt").read()
    from arpeggio.cleanpeg import ParserPEG
    parser = ParserPEG(grammar, "start", debug=False)
    return parser


exprParser = build_expr_parser()


class CalcVisitor(arpeggio.PTNodeVisitor):
    def visit_number(self, node, children):
        return arpeggio.text(node)

    def visit_id(self, node, children):
        return arpeggio.text(node)

    def visit_multiply(self, node, children):
        return "*" + children[0]

    def visit_add(self, node, children):
        return "+" + children[0]

    def visit_subtract(self, node, children):
        return "-" + children[0]

    def visit_divide(self, node, children):
        if len(children)>=2:
            dir = "up" if children[2] == "BigDecimal.ROUND_UP" else "down"
            return f"round_{dir}(% / {children[0]}, {children[1]})"
        return "/" + children[0]

    def visit_compareTo(self, node, children):
        cmp = children[1]
        value = int(children[2])
        other = children[0]
        # TODO check simplify algorithm here
        if value == 0:
            if cmp == '==':
                return f"(% == {other})"
            elif cmp == '!=':
                return f"(% != {other})"
            elif cmp == '>=':
                return f"(% >= {other})"
            elif cmp == '<=':
                return f"(% <= {other})"
        elif value < 0:
            if cmp == '==':
                return f"(% < {other})"
            elif cmp == '<=':
                return f"(% < {other})"
        elif value > 0:
            if cmp == '==':
                return f"(% > {other})"
            elif cmp == '>=':
                return f"(% > {other})"
        return f"compareTo(%, {other}, {value})"

    def visit_valueOf(self, node, children):
        return children[0]

    def visit_methods(self, node, children):
        return children[0]

    def visit_call(self, node, children):
        text = children[0]
        for c in children[1:]:
            if c[0] in "+-*/":
                text = f"({text}{c})"
            else:
                text = c.replace("%", text)
        return text

    def visit_var(self, node, children):
        if children == ['BigDecimal', 'ZERO']:
            return "0.0"

        if children == ['BigDecimal', 'ONE']:
            return "0.0"

        if len(children) == 2:
            return '.'.join(children)

        return children[0]

    def visit_arrayAccess(self, node, children):
        return children[0] + "[" + children[1] + "]"

    def visit_newBD(self, node, children):
        return children[0]

    def visit_term0(self, node, children):
        return children[0]

    def visit_term90(self, node, children):
        return ' */ '.join(children)

    def visit_term100(self, node, children):
        return ' +- '.join(children)

    def visit_term110(self, node, children):
        return ' '.join(children)

    def visit_term120(self, node, children):
        return ' '.join(children)

    def visit_term130(self, node, children):
        return ' && '.join(children)

    def visit_term140(self, node, children):
        return ' || '.join(children)

    def visit_setScale(self, node, children):
        dir = "up" if children[1] == "BigDecimal.ROUND_UP" else "down"
        return f"round_{dir}(%, {children[0]})"

    def visit_expression(self, node, children):
        return children[0]

    def visit_assign(self, node, children):
        return ' = '.join(children)

    def visit_start(self, node, children):
        return children[0]


with open("2022.xml") as fh:
    text = fh.read()


def replace(regex, replacement):
    global text
    r = re.compile(regex, re.DOTALL)
    text = re.sub(regex, replacement, text)

def translateExpr(x):
    v = parse(x.group(1))
    return f"{v};"


def translateIfExpr(x):
    b = parse(x.group(1))
    return f"if({b})"


def parse(value):
    structure = exprParser.parse(value)
    result = arpeggio.visit_parse_tree(structure, CalcVisitor(debug=False))
    # print(structure)
    return result

replace(r'<!--', r'/*')
replace(r'-->', r'*/')
replace(r'regex_test="" regex_transform=""', r'')
replace(r'<INPUT name="(.*)" type="(.*)" default="(.*)"\s*/>', r'\2 \1 = \3;')
replace(r'<INPUT name="(.*)" type="(.*)"\s*/>', r'\2 \1;')
replace(r'<OUTPUT name="(.*)" type="(.*)" default="(.*)"/>', r'\2 \1 = \3;')
replace(r'<OUTPUT name="(.*)" type="(.*)"/>', r'\2 \1;')
replace(r'<INTERNAL name="(.*)" type="(.*)" default="(.*)"/>', r'\2 \1 = \3;')
replace(r'<INTERNAL name="(.*)" type="(.*)"/>', r'\2 \1;')
replace(r'<CONSTANT name="(.*)" type="(.*)" value="(.*)"/>', r'\2 \1 = \3;')
replace(r'<CONSTANT name="(.*)" type="(.*)"/>', r'\2 \1;')
replace(r'<IF expr="(?P<c>.*)">', translateIfExpr)
replace(r'<THEN>', r'{')
replace(r'</THEN>', r'}')
replace(r'<ELSE>', r'else {')
replace(r'</ELSE>', r'}')
replace(r'<EVAL exec="(.*)"/>', translateExpr)
replace(r'<METHOD name="(.*)">', r'void \1() { ')
replace(r'</METHOD>', '}')
replace(r'</METHODS>', '')
replace(r'</IF>', '')
replace(r'</PAP>', '')
replace(r'</INPUTS>', '')
replace(r'</OUTPUTS>', '')
replace(r'</CONSTANTS>', '')
replace(r'<CONSTANTS>', '')
replace(r'<OUTPUTS type="STANDARD">', '')
replace(r'<OUTPUTS type="DBA">', '')
replace(r'<INTERNALS>', '')
replace(r'</INTERNALS>', '')
replace(r'</VARIABLES>', '')
replace(r'<METHODS>', '')
replace(r'<MAIN>', 'int main() {')
replace(r'</MAIN>', 'return 0; }')
replace(r'<EXECUTE method="(.*)"/>', r'\1();')
replace(r'<PAP name="Lohnsteuer2022Big" version="1.0" versionNummer="1.0">', '')
replace(r'<VARIABLES>', '')
replace(r'<INPUTS>', '')
replace(r'BigDecimal.ZERO', '0.0')
replace(r'BigDecimal.ONE', '1.0')
replace(r'BigDecimal\.valueOf\s*\(([0-9.]*)\)', r'(double)\1')
replace(r'new BigDecimal\((.*)\)', r'(double)\1')
replace(r'\((.*)\).compareTo\((.*)\) <= (.*)', r'(\1) - \2 <= \3')
replace(r'(.*).compareTo\((.*)\) <= (.*)', r'\1 - \2 <= \3')
replace(r'BigDecimal\[\] (.*?) =', r'BigDecimal \1[] =')
replace(r'BigDecimal', r'double')

print("#include <stdbool.h>")
print("#include <assert.h>")
#print("typedef double BigDecimal;")
print("""
double round_up(double value, int digits) {
    assert(digits < 3);
    if(digits == 0) {
        return (int) value + 1;
    } else
    if(digits == 1) {
        return (int) (10*value+1)/10;
    }else  if(digits == 2) {
        return (int) (100*value+1)/100;
    }
}

double round_down(double value, int digits) {
    assert(digits < 3);
    if(digits == 0) {
        return (int) value;
    } else  if(digits == 1) {
        return (int) (10*value)/10;
    } else  if(digits == 2) {
        return (int) (100*value)/100;
    }
}

void MPARA(); void MRE4JL(); void MSOLZSTS();
void MRE4(); void MRE4ABZ(); void MBERECH();
void MSONST(); void MVMT(); void MOSONST();
void STSMIN(); void  MRE4SONST(); void UPANTEIL();
void MSOLZ(); void UPTAB22(); void UP5_6();
void MST5_6(); void MVSP(); void UPEVP();
void UPTAB22(); void UPMLST();
void UPLSTLZZ(); void UPVKV();
void UPVKVLZZ(); 
void MZTABFB();
void MLSTJAHR();
void MLSTJAHR(); void MZTABFB(); void MRE4ALTE();
""")
print(text)


def test(input, expected):
    actual = parse(input)
    if actual.replace(' ', '') != expected.replace(' ', ''):
        print("ACTUAL:   ", actual)
        print("EXPRECTED:", expected)
        raise AssertionError()


test("ZRE4.subtract(ZVBEZ).compareTo(ZAHL1000) == -1", "((ZRE4-ZVBEZ) < ZAHL1000)")
test("ANP = ANP.add(ZRE4).subtract(ZVBEZ).setScale(0,BigDecimal.ROUND_UP)",
     "ANP=round_up(((ANP + ZRE4) - ZVBEZ),0)")

test("BigDecimal.valueOf(5.5).divide(ZAHL100)", "(5.5/ZAHL100)")

test("SOLZLZZ = SOLZLZZ.add(STS.multiply(BigDecimal.valueOf(5.5).divide(ZAHL100))).setScale(0, BigDecimal.ROUND_DOWN)",
     "SOLZLZZ = round_down((SOLZLZZ+(STS*(5.5/ZAHL100))), 0)")
