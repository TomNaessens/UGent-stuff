#!/bin/bash -ue

PRACT=0

if [ $# -ne 1 ]
then
	echo "Usage: $0 <GROUP>" 1>&2
	exit 1
fi
GROUP=$1

FILENAME=$(printf 'pract%.2i_group%.2i.tar.gz' $PRACT $GROUP)
FILES="Makefile main.c hash_table.h hash_table.c"

tar -czvf ${FILENAME} ${FILES}
echo
echo Done, tarball is named \'${FILENAME}\'
