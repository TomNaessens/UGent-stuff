#!/usr/bin/env python
# encoding: utf-8

# Usage: subtract.py FILE SUB SUB SUB ...
# Output in STDOUT

import sys

def readfile(f):
    with open(f) as fd:
        return set(fd.readlines())

if __name__ == "__main__":
    orig = readfile(sys.argv[1])
    for sf in sys.argv[2:]:
        sub = readfile(sf)
        orig -= sub
    for pept in orig:
        print(pept, end = "")
