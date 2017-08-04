#!/bin/bash

set -e

script_folder=`dirname $0`
pip install --user unidiff

if [ "$TRAVIS_PULL_REQUEST" == "false" ]; then
  $script_folder/run_diff.sh CPPLINT HEAD~1 # Check for errors introduced in last commit
else
  TMP_HEAD=$(git rev-parse HEAD)
  git config remote.origin.fetch +refs/heads/$TRAVIS_BRANCH:refs/remotes/origin/$TRAVIS_BRANCH
  git fetch
  git checkout $TMP_HEAD
  $script_folder/run_diff.sh CPPLINT origin/$TRAVIS_BRANCH # Check for errors compared to merge target
fi
