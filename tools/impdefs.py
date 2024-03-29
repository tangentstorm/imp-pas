# generate imp.defs
from __future__ import print_function
import re

rxDefn  = re.compile(r"^(procedure|function|operator)")
rxNewBlock = re.compile(r"{\$IFDEF IMPSHELL}")
rxEndBlock = re.compile(r"{\$ENDIF}")

inBlock = False

for line in open("imp.pas"):
    line = line.rstrip()
    if inBlock:
        if rxEndBlock.match(line): inBlock = False
        else: print(line)
    elif rxDefn.match(line):
        if line.count('.') : pass
        else: print(line.replace('forward;',''))
    elif rxNewBlock.match(line): inBlock = True
