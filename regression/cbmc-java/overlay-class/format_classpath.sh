#!/bin/bash

unameOut="$(uname -s)"
case "${unameOut}" in
    CYGWIN*)    separator=";";;
    MINGW*)     separator=";";;
    MSYS*)      separator=";";;
    Windows*)   separator=";";;
    *)          separator=":"
esac

echo -n `IFS=$separator; echo "$*"`
