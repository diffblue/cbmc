#!/bin/bash
echo "Compiling the helper file to extract the raw list of parameters from cbmc"
g++ -c -MMD -MP -std=c++11 -Wall -I ../../src/ -ftrack-macro-expansion=0 -fno-diagnostics-show-caret switch_extractor_helper.c  -o tmp.o 2> pragma.txt

retval=$?

#clean up compiled files, we don't need them.
rm tmp.o 2> /dev/null
rm tmp.d 2> /dev/null

#check if compilation went fine
if [ $retval -ne 0 ]; then
  echo "Problem compiling the helper file, parameter list not extracted."
  exit 1;
fi

echo "Converting the raw parameter list to the format required by autocomplete scripts"
rawstring=`sed "s/^.*pragma message: \(.*\)/\1/" pragma.txt`
#delete pragma file, we won't need it
rm pragma.txt 2> /dev/null

#now the main bit, convert from raw format to a proper list of switches
cleanstring=`(
  #extract 2-hyphen switches, such as --foo
  #grep for '(foo)' expressions, and then use sed to remove parantheses and put '--' at the start
  (echo $rawstring | grep -o "([^)]*)" | sed "s/^.\(.*\).$/--\1/") ;
  #extract 1-hyphen switches, such as -F
  #use sed to remove all (foo) expressions, then you're left with switches and ':', so grep the colons out and then use sed to include the '-'
  (echo $rawstring | sed "s/([^)]*)//g" | grep -o "[a-zA-Z0-9]" | sed "s/\(.*\)/-\1/")
 ) | tr '\n' ' '`

#sanity check that there is only one line of output
if [ `echo $cleanstring | wc -l | awk '{print $1}'` -ne 1 ]; then
 echo "Problem converting the parameter list to the correct format, I was expecting one line but either got 0 or >2. This is likely to be an error in this conversion script."
 exit 1;
fi

#sanity check that there are no dangerous characters
echo $cleanstring | grep -q "[^a-zA-Z0-9 -]"
if [ $? -eq 0 ]; then
 echo "Problem converting the parameter list to the correct format, illegal characters detected. This is likely to be an error in this conversion script."
 exit 1;
fi

echo "Injecting the parameter list to the autocomplete file."
sed "5 s/.*/  local switches=\"$cleanstring\"/" cbmc.sh.template > cbmc.sh

rm pragma.txt 2> /dev/null
