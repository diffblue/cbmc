#!/bin/bash

rm -f goto-magic goto-functions-* test test.c progress-* pid-* info-* \
  results.txt *.gb.linked.* *.tar *.tar.bz2

rm -rf success-* failure-*

rm -f nohup.out

rm -rf inst-0 inst-1

# Remove all unpacked folders
for F in *
do
  if [ -d "$F" ] && [ ${F:0:8} = 'goto-cc-' ]; then
    rm -rf "$F"
  fi
done

