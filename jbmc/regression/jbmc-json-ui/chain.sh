#!/bin/bash

JBMC_PATH=$1
shift

JQ_FILTER_FILE=$1
shift

$JBMC_PATH "$@" | jq -c -f $JQ_FILTER_FILE
