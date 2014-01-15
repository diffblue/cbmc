#!/bin/bash

parse_property_file()
{
  local fn=$1

  cat $fn | sed 's/[[:space:]]//g' | perl -n -e '
if(/^CHECK\(init\((\S+)\(\)\),LTL\(G(\S+)\)\)$/) {
  print "ENTRY=$1\n";
  print "PROPERTY=\"--error-label $1\"\n" if($2 =~ /^!label\((\S+)\)$/);
  print "PROPERTY=\"--pointer-check --memory-leak-check\"\n" if($2 =~ /^valid-(free|deref|memtrack)$/);
}'
}

parse_result()
{
  if tail -n 50 $LOG.ok | grep -q "^[[:space:]]*__CPROVER_memory_leak == NULL$" ; then
    echo 'FALSE(valid-memtrack)'
  elif tail -n 50 $LOG.ok | grep -q "^[[:space:]]*dereference failure:" ; then
    echo 'FALSE(valid-deref)'
  elif tail -n 50 $LOG.ok | grep -q "^[[:space:]]*double free$" ; then
    echo 'FALSE(valid-free)'
  elif tail -n 50 $LOG.ok | grep -q "^[[:space:]]*free argument has offset zero$" ; then
    echo 'FALSE(valid-free)'
  else
    echo FALSE
  fi
}

BIT_WIDTH="--64"
BM=""
PROP_FILE=""

while [ -n "$1" ] ; do
  case "$1" in
    --32|--64) BIT_WIDTH="$1" ; shift 1 ;;
    --propertyfile) PROP_FILE="$2" ; shift 2 ;;
    *) BM="$1" ; shift 1 ;;
  esac
done

if [ -z "$BM" ] || [ -z "$PROP_FILE" ] ; then
  echo "Missing benchmark or property file"
  exit 1
fi

if [ ! -s "$BM" ] || [ ! -s "$PROP_FILE" ] ; then
  echo "Empty benchmark or property file"
  exit 1
fi

eval `parse_property_file $PROP_FILE`
export ENTRY
export PROPERTY
export BIT_WIDTH
export BM

export LOG=`mktemp -t cbmc-log.XXXXXX`
trap "rm -f $LOG $LOG.latest $LOG.ok" EXIT

timeout 850 bash -c ' \
\
ulimit -v 15000000 ; \
\
EC=42 ; \
for c in 2 6 12 17 21 40 ; do \
  echo "Unwind: $c" > $LOG.latest ; \
  ./cbmc --unwind $c --no-unwinding-assertions $BIT_WIDTH $PROPERTY --function $ENTRY $BM >> $LOG.latest 2>&1 ; \
  ec=$? ; \
  if [ $ec -eq 0 ] ; then \
    if ! tail -n 10 $LOG.latest | grep -q "^VERIFICATION SUCCESSFUL$" ; then ec=1 ; fi ; \
  fi ; \
  if [ $ec -eq 10 ] ; then \
    if ! tail -n 10 $LOG.latest | grep -q "^VERIFICATION FAILED$" ; then ec=1 ; fi ; \
  fi ; \
\
  case $ec in \
    0) EC=0 ; mv $LOG.latest $LOG.ok ; echo "EC=$EC" >> $LOG.ok ;; \
    10) EC=10 ; mv $LOG.latest $LOG.ok ; echo "EC=$EC" >> $LOG.ok ; break ;; \
    *) if [ $EC -ne 0 ] ; then EC=$ec ; mv $LOG.latest $LOG.ok ; fi ; echo "EC=$EC" >> $LOG.ok ; break ;; \
  esac ; \
\
done \
'

if [ ! -s $LOG.ok ] ; then
  exit 1
fi
  
eval `tail -n 1 $LOG.ok`
cat $LOG.ok
case $EC in
  0) echo "TRUE" ;;
  10) parse_result ;;
  *) echo "UNKNOWN" ;;
esac
exit $EC

