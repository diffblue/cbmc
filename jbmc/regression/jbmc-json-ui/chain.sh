#!/bin/bash

JBMC_PATH=$1
shift

JQ_COMMAND=$1
shift

$JBMC_PATH "$@" | jq -c "$JQ_COMMAND"
