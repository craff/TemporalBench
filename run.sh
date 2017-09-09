#!/bin/bash

dir=`pwd`/..

file=$1
tool=$2
toolName=$3
timeout=$4
maxmem=$5
command=`echo $tool | { read first rest ; echo $first ; }`

out=$file.$toolName

line="$1"
TIMEFORMAT=%R

ulimit -Sv $maxmem
timefile=$(mktemp)
res=$(/usr/bin/time -v bash -c "timeout $timeout $tool < $file 2>&1" 2>$timefile)
echo $res
txt=$((echo $res | egrep -q "((unsat)|(not sat))" && echo unsat) ||
      (echo $res | egrep -q sat && echo sat) ||
      (echo timeout))

time=$(cat $timefile)
rm $timefile

SecRe='User time [(]seconds[)]: ([0-9.]+)'

timeSec=$(echo "$time" | while read line; do
    if [[ $line =~ $SecRe ]]; then
	echo ${BASH_REMATCH[1]}
    fi
done)

MemRe='Maximum resident set size [(]kbytes[)]: ([0-9]+)'

timeMem=$(echo "$time" | while read line; do
    if [[ $line =~ $MemRe ]]; then
	echo ${BASH_REMATCH[1]}
    fi
done)

toolDate=$(stat -c %Y $command)

sql="INSERT INTO runs (tool,file,toolDate,time,mem,timeAllowed,memAllowed,result,fullOutput) VALUES ('$toolName','$file',FROM_UNIXTIME($toolDate),'$timeSec','$timeMem','$timeout','$maxmem','$txt','$res')"

echo $sql | mysql solver --user=solver

echo $file $tool: $txt $timeSec $timeMem

echo Result: "$txt" > $out
echo "$time" >> $out
echo >> $out
echo Original output: >> $out
echo "$res" >> $out
