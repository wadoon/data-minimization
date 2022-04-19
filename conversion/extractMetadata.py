#!/usr/bin/python3
import re
import sys

import yaml

meta = {'INPUTS': {}, 'OUTPUTS': {}, 'INTERNALS': {}, 'FACTS': []}

with open("2022.xml") as fh:
    text = fh.read()


def find(pattern: str, cat: str):
    regex = re.compile(pattern)
    for name, type in regex.findall(text):
        meta[cat][name] = 0.0


find(r'<INPUT name="(.*?)" type="(.*?)"', "INPUTS")
find(r'<OUTPUT name="(.*?)" type="(.*?)"', "OUTPUTS")
find(r'<INTERNAL name="(.*?)" type="(.*?)"', "INTERNALS")

yaml.safe_dump(meta, sys.stdout)
