#!/bin/bash

function getVMs() {
    onevm list | tail -n +2 | tr -s " " "," | sed "s/,//" | cut -f1 -d',' | tr "\\n" " "
}
