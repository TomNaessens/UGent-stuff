#!/usr/bin/env python
# encoding: utf-8

"""Print the content intersection of a set of files"""

from functools import reduce


def line_set(file_name):
    """Construct a set of all lines in a files"""
    with open(file_name) as file_:
        return set(file_.readlines())


if __name__ == '__main__':
    import sys

    line_sets = (line_set(file_) for file_ in sys.argv[1:])
    intersection = reduce(set.intersection, line_sets)

    for element in intersection:
        print(element, end='')
