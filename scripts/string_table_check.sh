#!/bin/bash

whitelist=" \
"

cleanup()
{
  rm -f "$ids_file"
}

ids_file=$(mktemp)

trap cleanup EXIT

gcc -E -P -x c src/util/irep_ids.def \
  -D'IREP_ID_ONE(x)=ID_ ## x' -D'IREP_ID_TWO(x,y)=ID_ ## x' > $ids_file

for w in $whitelist
do
  perl -p -i -e "s/^$w\n//" $ids_file
done

for i in $(<$ids_file)
do
  if ! git grep -w -q -c -F $i
  then
    echo "$i is never used"
    exit  1
  fi
done
