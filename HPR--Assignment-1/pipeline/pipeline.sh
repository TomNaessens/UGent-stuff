#!/bin/bash
#PBS -N Pipeline
#PBS -l nodes=1:ppn=1
#PBS -N normal
#PBS -o output.file
#PBS -e error.file
#PBS -l walltime=1:00:00
#PBS -m be

$VSC_HOME/HPR--Assignment-1/pipeline/pipeline
