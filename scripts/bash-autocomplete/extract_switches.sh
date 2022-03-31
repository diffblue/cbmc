#!/bin/bash

set -e

# make sure we execute the remainder in the directory containing this script
cd `dirname $0`

echo "Compiling the helper file to extract the raw list of parameters from cbmc"
g++ -E -dM -std=c++11 -I../../src ../../src/cbmc/cbmc_parse_options.cpp -o macros.c
echo CBMC_OPTIONS >> macros.c

echo "Converting the raw parameter list to the format required by autocomplete scripts"
rawstring="`gcc -E -P -w macros.c` \"?h(help)\""
rm macros.c

#now the main bit, convert from raw format to a proper list of switches
cleanstring=`(
  #extract 2-hyphen switches, such as --foo
  #grep for '(foo)' expressions, and then use sed to remove parantheses and put '--' at the start
  (echo $rawstring | grep -o "([^)]*)" | sed "s/^.\(.*\).$/--\1/") ;
  #extract 1-hyphen switches, such as -F
  #use sed to remove all (foo) expressions, then you're left with switches and ':', so grep the colons out and then use sed to include the '-'
  (echo $rawstring | sed "s/([^)]*)//g" | grep -o "[a-zA-Z0-9?]" | sed "s/\(.*\)/-\1/")
 ) | tr '\n' ' '`

#sanity check that there is only one line of output
if [ `echo $cleanstring | wc -l | awk '{print $1}'` -ne 1 ]; then
 echo "Problem converting the parameter list to the correct format, I was expecting one line but either got 0 or >2. This is likely to be an error in this conversion script."
 exit 1;
fi

#sanity check that there are no dangerous characters
if echo $cleanstring | grep -q "[^a-zA-Z0-9? -]"; then
 echo "Problem converting the parameter list to the correct format, illegal characters detected. This is likely to be an error in this conversion script."
 exit 1;
fi

echo "Injecting the parameter list to the autocomplete file."
sed "5 s/.*/  local switches=\"$cleanstring\"/" cbmc.sh.template > cbmc.sh
