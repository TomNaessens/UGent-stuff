#!/bin/bash

usage() {
  echo "Usage: ./dot.sh $PROGRAM.c"
  exit 1
}

[[ ! $# -eq 1 ]] && usage

make $1
opt -dot-cfg $1
xdot cfg.main.dot
