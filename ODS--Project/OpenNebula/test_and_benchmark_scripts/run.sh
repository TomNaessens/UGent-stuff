#!/bin/bash

AVMS=$1 # amount of vms
POLLTIME=5m # log time in time
RUNTIME=24 # running time in x-amount of polltimes
LOGFILE="log.$AVMS.txt"

# Remove the old log file
rm $LOGFILE 2> /dev/null
# And create a new one
touch $LOGFILE
date >> $LOGFILE

# Create
./create.sh $AVMS >> $LOGFILE

# Sleep 10 minutes to make sure the VMs are loaded

for ((i=0; i<$RUNTIME; i++))
do
  ./log.sh $LOGFILE
  sleep $POLLTIME
done

./log.sh $LOGFILE

./manage.sh "delete" >> $LOGFILE

./log.sh $LOGFILE
