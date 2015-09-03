#!/bin/bash

set -eu

FOLDERS="data/*"
RESULT_FOLDER="results"

for folder in $FOLDERS
do
  folder_name=$(basename $folder)

  FILES="$folder/*"

  mkdir -p "$RESULT_FOLDER/$folder_name"

  for file in $FILES
  do
    file_name=$(basename $file)
    echo "Processing $file_name"

    (cat $file | grep -v "^>" | prot2pept | peptfilter | sort | uniq > "$RESULT_FOLDER/$folder_name/$file_name.pepts") &
  done
done

wait
