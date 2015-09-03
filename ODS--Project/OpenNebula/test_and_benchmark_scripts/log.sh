#!/bin/bash

LOGFILE=$1

echo "" >> $LOGFILE
date >> $LOGFILE
onevm list >> $LOGFILE
