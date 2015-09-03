#! /bin/bash
awk '/>/ { hdr = $1; sub(/>ENSP/, "", hdr); printf("\n%s ", hdr) } !/>/ { printf("%s", $0) }' | tail -n+2 | sort -k2
