#!/bin/bash

# Run tool on all of Michael's Debian packages.
#
# goto-runner.sh <id> <line-start> <line-stop>
#
# <id>: natural; id of this instance
# <line-start>: line at which to start in $FILE_LIST (1-based)
# <line-stop>: line at which to stop in $FILE_LIST (inclusive)
#
# Produced files:
# - progress-*: progress
# - info-*: logfile of the script
# - pid-*: pid of the script
# - in success-*/*: output of successful runs
# - in failure-*/*: output of unsuccessful runs
#
# Progress format (updated when a new package is handled):
# (line-start) current line / line-stop (total lines)
# ...

# ------------------------------------------------------------------------------
# Config

. "$(hostname).config" || exit 1

# ------------------------------------------------------------------------------
# Misc

error() {
  echo $PRE "$1" >&2
}

inf() {
  echo $PRE "$1"
}

bail() {
  error "$1"
  exit 1
}

usage() {
  echo -e '\nUsage:' >&2
  echo -e '  goto-runner.sh <id> <line-start> <line-stop>\n' >&2
}

natcheck() {
  echo "$1" | egrep -q '^(0|([1-9][0-9]*))$' > /dev/null 2>&1
  [ $? -ne 0 ] && bail 'not a natural number'
}

# Replace forward slashes with underscores
replace() {
  echo "$1" | sed 's/\//\_/g'
}

# ------------------------------------------------------------------------------
# Handle arguments

PRE='goto-runner:'

if [ $# -ne 3 ]; then
  error 'number of arguments != 3'
  usage
  exit 1
fi

I="$1"
LSTART="$2"
LSTOP="$3"

natcheck "$I"
natcheck "$LSTART"
natcheck "$LSTOP"

if [ "$LSTART" -eq 0 ]; then
  error 'line-start must be >= 1'
  usage
  exit 1
fi
if [ "$LSTART" -gt "$LSTOP" ]; then
  error'line-start greater than line-stop'
  usage
  exit 1
fi

TN=${#FE[@]}

# ------------------------------------------------------------------------------
# Signal handling

STOP=0

grace() {
  inf 'Termination signal received; will exit after this iteration'
  STOP=1
}

trap grace SIGINT SIGTERM

# ------------------------------------------------------------------------------
# Sanity checks

N=$TN
for ((i=0; i<N; i++))
do
  TOOL[$i]="${FE[$i]}"
done
TOOL[$N]="$GI"
N=$(($N + 1))
TOOL[$N]="$GC"

for T in "${TOOL[@]}"
do
  $T > /dev/null 2>&1
  [ $? -eq 127 ] && bail "Cannot invoke $T"
done

[ ! -f "$PTHREAD_LIB" ] && bail 'pthread lib file does not exist'
[ ! -f "$PTHREAD_LIB_ALT" ] && bail 'alt pthread lib file does not exist'

natcheck "$FACTOR"

# ------------------------------------------------------------------------------
# Preparation

ulimit -v $MAXMEM

INFO="info-$I"
PROG="progress-$I"

[ -e $INFO ] && bail "file $INFO already exists (delete it to start afresh)"
[ ! -r $FILE_LIST ] && bail "file $FILE_LIST cannot be opened for reading"

> $INFO
> $PROG

echo '# vim: nowrap' >> $INFO

# Directories for output files
mkdir success-$I > /dev/null 2>&1
mkdir failure-$I > /dev/null 2>&1

# Magic
echo '0 bequad 0x7f47424600000002 goto-binary-old' > goto-magic
echo '0 belong 0x7f474246 goto-binary' > goto-magic
echo 'int main() {}' > test.c
$GC test.c -o test > /dev/null 2>&1
file -m goto-magic test 2>&1 | grep 'goto-binary' > /dev/null 2>&1
[ $? -ne 0 ] && bail 'goto magic failed'

TOTAL=$(wc -l $FILE_LIST | cut -f 1 -d ' ')
NUM=$(($LSTOP - $LSTART + 1))
COUNT=$LSTART

FILES=$(tail -n +$LSTART $FILE_LIST | head -n $NUM)

# Number of files handled so far
FILE_COUNT=0

# Number of goto binaries handled so far
GB_COUNT=0

# Number of goto binaries suitable for tool so far
FE_COUNT=0

MAIN_COUNT=0
PTHREAD_COUNT=0
LOC_COUNT=0

PKG_URL_COUNT=0
PKG_SIZE_COUNT=0
PKG_DOWN_COUNT=0

for ((i=0; i<TN; i++))
do
  # Number of successes
  SUC_COUNT[$i]=0
  # Number of terminations through timeout
  TO_COUNT[$i]=0
  # Number of terminations through error (e.g. crash, out of memory)
  CRASH_COUNT[$i]=0
done

echo $$ > pid-$I

# ------------------------------------------------------------------------------
# Progress

print-progress() {
  echo -e "($LSTART) $COUNT / $LSTOP ($TOTAL)\n" > $PROG

  echo "Packages at URL: $PKG_URL_COUNT" >> $PROG
  echo "^ + size within bounds: $PKG_SIZE_COUNT" >> $PROG
  echo -e "^ + package downloaded: $PKG_DOWN_COUNT\n" >> $PROG  

  echo "Files within packages: $FILE_COUNT" >> $PROG
  echo "^ + is a goto binary: $GB_COUNT" >> $PROG
  echo "^ + main: $MAIN_COUNT" >> $PROG
  echo "^ + pthread_create: $PTHREAD_COUNT" >> $PROG
  echo "^ + loc size within bounds: $LOC_COUNT" >> $PROG
  echo -e "^ + linking successful: $FE_COUNT\n" >> $PROG

  local i=0
  for ((i=0; i<TN; i++))
  do
    echo "$i success: ${SUC_COUNT[$i]}" >> $PROG
    echo "$i timeout: ${TO_COUNT[$i]}" >> $PROG
    echo "$i error: ${CRASH_COUNT[$i]}" >> $PROG
  done
}

# ------------------------------------------------------------------------------
# Exploration

# Download packages and perform checks (for all lines in $FILE_LIST)
for L in $FILES
do
  print-progress

  echo -e "\n>>> PACKAGE: $L ($COUNT)\n" >> $INFO

  COUNT=$(($COUNT + 1))

  # Produce URL and archive name
  URL="$BEFORE$L$AFTER"
  ARCHIVE="${L}.tar.bz2"

  # Check if archive exists
  wget --spider -nv --timeout=60 "$URL" > /dev/null 2>&1
  if [ $? -ne 0 ]; then
    echo "$L: package does not exist at URL (or network problems)" >> $INFO
    continue
  fi

  PKG_URL_COUNT=$(($PKG_URL_COUNT + 1))

  ARCHIVE_SIZE=$(wget --spider --timeout=60 "$URL" 2>&1)
  if [ $? -ne 0 ]; then
    echo "$L: error on checking archive size" >> $INFO
    continue
  fi
  ARCHIVE_SIZE=$(echo "$ARCHIVE_SIZE" | grep 'Length:' | sed -r \
    's/(^Length: | \(.*$)//g')
  natcheck "$ARCHIVE_SIZE"
  if [ "$ARCHIVE_SIZE" -gt "$MAX_ARCHIVE_SIZE" ]; then
    echo "$L: archive size exceeds maximum size" >> $INFO
    continue
  fi

  PKG_SIZE_COUNT=$(($PKG_SIZE_COUNT + 1))

  wget -nv --timeout=60 "$URL" -O "$ARCHIVE" > /dev/null 2>&1
  if [ $? -ne 0 ]; then
    echo "$L: download error" >> $INFO
    rm -f "$ARCHIVE"
    continue
  fi

  PKG_DOWN_COUNT=$(($PKG_DOWN_COUNT + 1))

  # Unpack archive
  mkdir "$L"
  if [ $? -ne 0 ]; then
    echo "$L: cannot create dir for unpacking" >> $INFO
    continue
  fi
  tar xj -C "$L" -f "$ARCHIVE"
  if [ $? -ne 0 ]; then
    echo "$L: cannot untar archive" >> $INFO
    continue
  fi
  if [ ! -d "$L/goto-binaries" ]; then
    echo "$L: unexpected dir" >> $INFO
    continue
  fi

  echo -e 'package ok\n' >> $INFO

  # Traverse files in package
  PKGFILES=$(find "$L/goto-binaries" -type f)
  for F in $PKGFILES
  do
    print-progress

    FILE_COUNT=$(($FILE_COUNT + 1))

    file -m goto-magic "$F" 2>&1 | grep 'goto-binary' > /dev/null 2>&1
    # If file is a goto binary
    if [ $? -eq 0 ]; then
      
      GB_COUNT=$(($GB_COUNT + 1))

      # Size of the binary
      SIZE=$(wc -c "$F" | cut -d ' ' -f 1)
      natcheck $SIZE
      if [ $SIZE -gt $MAX_GB_SIZE ]; then
        echo "$L: $F: Goto binary exceeds maximum size" >> $INFO
        continue
      fi

      timeout -k 5 30 $GI --show-goto-functions "$F" > goto-functions-$I 2> \
        /dev/null
      if [ $? -ne 0 ]; then
        # Most likely out of memory (ignore this binary and go to next one)
        echo "$L: $F: Cannot get goto functions" >> $INFO
        continue
      fi

      # Check if there is a main function (invocation)
      egrep 'main[\ ]?((\([\ ]?\))|(\(.+,.+\)))' goto-functions-$I > /dev/null \
        2>&1
      if [ $? -ne 0 ]; then
        echo "$L: $F: No main()" >> $INFO
        continue
      fi

      MAIN_COUNT=$(($MAIN_COUNT + 1))

      # Check if there is an invocation of pthread_create
      egrep 'pthread_create[\ ]?\(.+,.+,.+,.+\)' goto-functions-$I > /dev/null \
        2>&1
      if [ $? -ne 0 ]; then
        echo "$L: $F: No pthread_create()" >> $INFO
        continue
      fi

      PTHREAD_COUNT=$(($PTHREAD_COUNT + 1))

      # LoC
      LOC=$(timeout -k 5 30 $GI --count-eloc "$F" 2> /dev/null)
      if [ $? -ne 0 ]; then
        echo "$L: $F: Error on counting LoC" >> $INFO
        continue
      fi
      LOC=$(echo "$LOC" | tail -n 1 | cut -d ' ' -f 5)
      natcheck "$LOC"
      if [ $LOC -gt $MAX_LOC ]; then
        echo "$L: $F: Goto binary LoC exceeds maximum" >> $INFO
        continue
      fi

      LOC_COUNT=$(($LOC_COUNT + 1))

      # Change name (CBMC/goto-cc bug workaround)
      mv "$F" "$F.gb"
      F="$F.gb"

      # Link with pthreads lib
      $GC -o "$F.linked" "$F" "$PTHREAD_LIB"
      if [ $? -ne 0 ]; then
        echo "$L: $F: Linking error, trying next pthread lib" >> $INFO
        $GC -o "$F.linked" "$F" "$PTHREAD_LIB_ALT"
        if [ $? -ne 0 ]; then
          echo "$L: $F: Linking error, giving up" >> $INFO
          continue
        fi 
      fi
      F="$F.linked"

      # Increment number of goto binaries suitable for tool
      FE_COUNT=$(($FE_COUNT + 1))

      echo "@@@ Running tools on $L: $F." >> $INFO
      echo "@@@ LoC: $LOC" >> $INFO
      echo "@@@ Binary size (in bytes): $SIZE" >> $INFO 

      # ------------------------------------------------------------------------
      # Invoke tools

      TN1=$(($TN - 1))

      # Running list
      PIDS=""

      # Pid to idx
      declare -A PM

      for ((i=0; i<TN; i++))
      do
        # Create invocation and start process
        mkdir "inst-$i"; cd "inst-$i"
        OUT=$(replace "$F")
        INV="${FE[$i]}" 
        INV="/usr/bin/time -p timeout -k 5 $TIMEOUT $INV ../$F > $OUT.$i 2>&1"
        echo "@@@: Invocation '$INV'" >> ../$INFO
        bash -c "ulimit -v $MAXMEM_FE; $INV" &
        P=$!
        PIDS="$PIDS $P"
        PM[$P]=$i
        cd ..

        # Continue if <= parallel factor and we have not invoked all
        R=$(($R + 1))
        if [ $R -lt $FACTOR ] && [ $i -lt $TN1 ]; then
          continue
        fi  

        while true; do
          for P in $PIDS
          do
            kill -0 $P > /dev/null 2>&1
            if [ $? -ne 0 ]; then
              wait $P
              RET=$?
              IDX=${PM[$P]}
              # Attempt to kill process just to be sure
              kill -9 $P > /dev/null 2>&1
              PIDS=$(echo "$PIDS" | sed "s/$P//g")
              R=$(($R - 1))
              cd "inst-$IDX"
              # Harvest results
              if [ $RET -eq 0 ]; then
                echo "@@@: Success on $F ($IDX) (return code 0)" >> ../$INFO
                mv "$OUT.$IDX" ../success-$I
                if [ -f results.txt ]; then
                  mv results.txt ../success-$I/"$OUT.$IDX.res"
                fi
                SUC_COUNT[$IDX]=$((${SUC_COUNT[$IDX]} + 1))
              else
                echo "@@@: Failure on $F ($IDX) (return code $RET)" >> ../$INFO
                mv "$OUT.$IDX" ../failure-$I
                if [ $RET -eq 124 ] || [ $RET -eq 137 ]; then
                  TO_COUNT[$IDX]=$((${TO_COUNT[$IDX]} + 1))
                else
                  CRASH_COUNT[$IDX]=$((${CRASH_COUNT[$IDX]} + 1))
                fi
              fi
              cd ..
              rm -rf "inst-$IDX"
              print-progress
              if [ $i -lt $TN1 ]; then
                continue 3
              fi
              if [ -z "${PIDS// /}" ]; then
                break 2
              fi
            fi
          done
          sleep 3
        done
      done

      # ------------------------------------------------------------------------

    else
      echo "$L: $F: Not a goto binary" >> $INFO
    fi # If file is a goto binary
  done # For all files in package

  # Delete archive and unpacked files
  if [ $KEEP -eq 0 ]; then
    # Downloaded archive
    rm -rf "$ARCHIVE"
    # Directory were archive was unpacked to
    rm -rf "$L"
  fi

  # delete goto functions dumped by goto-instrument
  rm -f goto-functions-$I

  if [ $STOP -eq 1 ]; then
    break
  fi
done

# Cleanup before termination
rm -f goto-magic

print-progress

