#!/bin/bash

HYLORESPATH="../dist/build/hylores/hylores" # path to HyLoRes
UNSATPATH="sat"              # directory where examples are

for file in `ls ${UNSATPATH}/*.frm`;
do echo $file;spartacus --intohyloFile=$file $1 $2 $3 $4;
done


