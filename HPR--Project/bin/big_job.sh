#!/bin/sh
#
#
#PBS -N mpi64
#PBS -o output64.file
#PBS -e error64.file
#PBS -l nodes=4:ppn=16
#PBS -l walltime=5:00:00
#

module load ictce
module load VSC-tools
mympirun $VSC_HOME/HPR--Project/bin/solution $VSC_HOME/HPR--Project/misc/X_mmSchools.txt $VSC_HOME/HPR--Project/misc/Y_mmSchools.txt $VSC_HOME/HPR--Project/misc/Z_mmSchools.txt
