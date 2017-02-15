#!/bin/bash

set -e

gcc $1 -o a.out
./a.out
