#!/bin/bash

set -e

if [ $# -ne 1 ]
then
  echo "Target directory required" 1>&2
  exit 1
fi

if ! make -s generated_files
then
  echo "Failed to run 'make generated_files'" 1>&2
  exit 1
fi

DEST=$1

gen_makefile()
{
  local d=$1
  local m=$2

  mkdir -p $DEST/src/$d
  cat > $DEST/src/$d/$m <<EOF
VPATH =
vpath %.cpp $PWD/$d
vpath %.cc $PWD/$d
vpath %.h $PWD/$d
vpath %.y $PWD/$d
vpath %.l $PWD/$d
vpath %.txt $PWD/$d
EOF
  cat $d/$m >> $DEST/src/$d/$m
}

makefiles=$(find . -name Makefile | grep -v $DEST)

for m in $makefiles
do
  dir=$(dirname $m)
  gen_makefile $dir Makefile
done

gen_makefile big-int makefile

cp common config.inc $DEST/src/

# tweak include paths in config.inc
perl -p -i -e 's/(= \.\.\/\.\.\/)/$1..\/..\//' $DEST/src/config.inc
echo "INCLUDES += -I$PWD" >> $DEST/src/config.inc

# tweak targets that aren't compatible with vpaths
perl -p -i -e "s{(library/\\*.c)}{$PWD/ansi-c/\$1}" $DEST/src/ansi-c/Makefile
perl -p -i -e 's/^(cprover_library.inc:)/%$1/' $DEST/src/ansi-c/Makefile
perl -p -i -e 's/^(cprover_library.cpp:)/#$1/' $DEST/src/ansi-c/Makefile

perl -p -i -e 's/^(irep_ids.cpp:)/#$1/' $DEST/src/util/Makefile

# create sub-directories
mkdir -p $DEST/src/ansi-c/library $DEST/src/ansi-c/literals
mkdir -p $DEST/src/goto-instrument/{accelerate,wmm}
mkdir -p $DEST/src/solvers/{flattening,floatbv,miniBDD,prop,qbf,refinement,sat,smt1,smt2}

# copy generated files for coverage reports
for f in \
  ansi-c/ansi_c_lex.yy.cpp ansi-c/scanner.l ansi-c/ansi_c_y.tab.cpp \
  assembler/scanner.l assembler/assembler_lex.yy.cpp \
  jsil/jsil_lex.yy.cpp jsil/scanner.l jsil/jsil_y.tab.cpp \
  json/parser.y json/json_lex.yy.cpp json/json_y.tab.cpp \
  xmllang/scanner.l xmllang/xml_lex.yy.cpp xmllang/xml_y.tab.cpp xmllang/parser.y
do
  cp $f $DEST/src/$(dirname $f)/
done

cp -aL ../regression $DEST/
