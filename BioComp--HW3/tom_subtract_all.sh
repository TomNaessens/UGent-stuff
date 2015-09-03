#!/bin/bash

python3 subtract.py results/unique_breast.pepts results/formula/* | sort > results/unique_breast_minus_formula.pepts
python3 subtract.py results/unique_formula.pepts results/breast/* | sort > results/unique_formula_minus_breast.pepts
