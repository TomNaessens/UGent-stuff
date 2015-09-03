#!/bin/bash
module load ictce
mpirun -np 6 ./solution ../misc/sX_mmSchools.txt ../misc/sY_mmSchools.txt ../misc/sZ_mmSchools.txt
