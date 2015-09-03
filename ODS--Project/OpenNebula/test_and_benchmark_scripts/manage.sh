#!/bin/bash

. helpers.sh

function doWithAll() {
    action=$1

    for vm in $(getVMs)
    do
      onevm $action $vm
    done
}

doWithAll $1
