#!/bin/bash
awk '{printf("%s ", $1); print length($2)}'
