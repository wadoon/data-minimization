#!/usr/bin/python3
import re
import sys
import xml.sax as x
from xml.sax.handler import ContentHandler
from xml.sax.xmlreader import AttributesImpl

import yaml

meta = {'INPUTS': {}, 'OUTPUTS': {}, 'INTERNALS': {}, 'FACTS': []}


class Handler(ContentHandler):
    def startElement(self, name, attrs: AttributesImpl):
        target = None
        if name == 'INPUT':
            target = 'INPUTS'
        elif name == 'OUTPUT':
            target = 'OUTPUTS'
        elif name == 'INTERNAL':
            target = 'INTERNALS'

        if target:
            meta['INPUTS'][attrs['name']] = attrs.get('default', '0.0')


with open("2022.xml") as fh:
    # x.parse(fh, Handler())
    text = fh.read()


def find(pattern: str, cat: str):
    regex = re.compile(pattern)
    for name, type in regex.findall(text):
        meta[cat][name] = 0.0


find(r'<INPUT name="(.*?)" type="(.*?)"', "INPUTS")
find(r'<OUTPUT name="(.*?)" type="(.*?)"', "OUTPUTS")
find(r'<INTERNAL name="(.*?)" type="(.*?)"', "INTERNALS")

yaml.safe_dump(meta, sys.stdout)
