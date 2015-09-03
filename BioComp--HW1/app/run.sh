#!/bin/sh
#
#
#PBS -N array
#PBS -o output/output.file
#PBS -e error/error.file
#PBS -l walltime=6:00:00
#PBS -m be
#


i=$PBS_ARRAYID
chunkSize=250

cd $PBS_O_WORKDIR

module load Python/2.7.6-ictce-5.5.0
python app.py $i $chunkSize > $VSC_DATA/famous_wordlist/output.$i.txt
