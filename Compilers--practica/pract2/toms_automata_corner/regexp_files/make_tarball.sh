#!/bin/bash -ue

PRACT=2

if [ $# -ne 1 ]
then
	echo "Usage: ./$0 <GROUP>" 1>&2
	exit 1
fi
GROUP=$1

FILENAME=$(printf 'pract%.2i_group%.2i.tar.gz' $PRACT $GROUP)
FILES="token_a.jff token_b.jff token_c.jff nfa.jff nfa2dfa.csv
       dfa.jff dfa-answer.txt"

tar -czvf ${FILENAME} ${FILES}
echo Done, tarball is named \'${FILENAME}\'
