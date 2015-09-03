#!/bin/bash

set -eu
cd $(dirname ${BASH_SOURCE})

./make_peptides.sh
./tom_create_intersect.sh
./tom_subtract_all.sh
