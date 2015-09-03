#!/bin/bash
module load ictce
mpirun -np 6 ./solution ../misc/X_mmSchools.txt ../misc/Y_mmSchools.txt ../misc/Z_mmSchools.txt
