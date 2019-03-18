#!/bin/bash

_term() {
  # Remove the handler first
  trap - SIGTERM SIGINT
  # Note use of negative PID to forward the kill signal to the whole process group
  kill -TERM -$child
}

trap _term SIGTERM SIGINT

export TIME="%U"

# setsid: start the child in a fresh group, so we can kill its whole group when
# signalled
setsid -w /usr/bin/time --quiet -o tmp_time.out "$@" &
child=$!

# Need to use 'wait' so we can receive signals
wait $child
