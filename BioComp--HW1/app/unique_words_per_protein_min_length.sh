#!/bin/bash
cut -d' ' -f1,2 | grep "^[^ ]* .\{$1\}.*$" | uniq | awk '{ if(header == $1) { printf(" %s", $2) } else { printf("\n%s", $0); header = $1 } } END {printf("\n")}' | tail -n+2
