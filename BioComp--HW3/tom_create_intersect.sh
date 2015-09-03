#!/bin/bash

set -eu

FOLDERS="results/*/"
RESULT_FOLDER="results"

for folder in $FOLDERS
do
  folder_name=$(basename $folder)

  FILES=( $folder/* )
  FILE_AMOUNT=${#FILES[@]}

  echo "Processing $folder_name"

  (sort ${FILES[@]} |\
      uniq -c |\
      sed 's/^ *//' |\
      grep "^\(${FILE_AMOUNT}\|$((FILE_AMOUNT - 1))\) " |\
      cut -f2 -d' ' \
      > "$RESULT_FOLDER/unique_$folder_name.pepts") &
done

wait
