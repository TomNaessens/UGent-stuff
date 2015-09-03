#!/bin/sh
#
#
#PBS -N mpi
#PBS -o output.file
#PBS -e error.file
#PBS -l nodes=1:ppn=1
#PBS -l walltime=5:00:00
#

module load ictce
module load VSC-tools
mympirun $VSC_HOME/HPR--Project/bin/solution $VSC_HOME/HPR--Project/misc/sX_mmSchools.txt $VSC_HOME/HPR--Project/misc/sY_mmSchools.txt $VSC_HOME/HPR--Project/misc/sZ_mmSchools.txt
