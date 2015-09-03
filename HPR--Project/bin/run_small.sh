#!/bin/bash
module load ictce
mpirun -np 2 ./solution ../misc/ssX.txt ../misc/ssY.txt ../misc/ssZ.txt
