#!/bin/bash

for file in `ls prof/*.frm`;
do echo $file;./hylores -t 30 -f $file $1 $2 $3 $4 +RTS -p -RTS; mv hylores.prof $file.prof;
done

