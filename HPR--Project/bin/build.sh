#!/bin/bash
module load ictce
mpiicpc ../src/solution.cpp -o solution -L$MKLROOT/mkl/lib/intel64/ -lmkl_scalapack_lp64 -lmkl_intel_lp64 -lmkl_core -lmkl_sequential -lmkl_blacs_intelmpi_lp64 -lpthread -lm
