#!/bin/bash

set -e

script_folder=`dirname $0`
pip install --user unidiff

if [ "$TRAVIS_PULL_REQUEST" == "false" ]; then
  $script_folder/run_diff.sh CPPLINT HEAD~1 # Check for errors introduced in last commit
else
  TMP_HEAD=$(git rev-parse HEAD)
  git config remote.origin.fetch +refs/heads/$TRAVIS_BRANCH:refs/remotes/origin/$TRAVIS_BRANCH
  git fetch --unshallow
  git checkout $TMP_HEAD
  MERGE_BASE=$(git merge-base ${TRAVIS_COMMIT_RANGE%...*} ${TRAVIS_COMMIT_RANGE#*...})
  $script_folder/run_diff.sh CPPLINT $MERGE_BASE
fi
