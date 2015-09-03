#!/bin/bash

number=$1
image=one-templates/ttylinux.one

for ((i=0; i<$number; i++))
do
  onevm create $image
done
