#!/bin/bash
awk '{ print length($2) " " $2; }' | sort -n | uniq
