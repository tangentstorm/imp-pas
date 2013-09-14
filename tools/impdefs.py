# generate imp.defs
from __future__ import print_function
import re

rxDefn  = re.compile(r"^(procedure|function)")
rxNewBlock = re.compile(r"{\$IFDEF IMPSHELL}")
rxEndBlock = re.compile(r"{\$ENDIF}")

inBlock = False

for line in open("imp.pas"):
    line = line.rstrip()
    if inBlock:
        if rxEndBlock.match(line): inBlock = False
        else: print(line)
    elif rxDefn.match(line):
        print(line.replace('forward;',''))
    elif rxNewBlock.match(line): inBlock = True
