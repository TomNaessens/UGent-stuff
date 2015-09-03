#!/bin/bash
cut -f1,2 -d' ' * | uniq | cut -f1 -d' ' | uniq -c
