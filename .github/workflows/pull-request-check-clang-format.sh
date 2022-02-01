#!/bin/bash

# Stop on errors
set -e

# Log information about the run of this check.
echo "Pull request's base branch is: ${BASE_BRANCH}"
echo "Pull request's merge branch is: ${MERGE_BRANCH}"
echo "Pull request's source branch is: ${GITHUB_HEAD_REF}"
clang-format-10 --version

# The checkout action leaves us in detatched head state. The following line
# names the checked out commit, for simpler reference later.
git checkout -b ${MERGE_BRANCH}

# Build list of files to ignore 
while read file ; do EXCLUDES+="':(top,exclude)$file' " ; done < .clang-format-ignore

# Make sure we can refer to ${BASE_BRANCH} by name
git checkout ${BASE_BRANCH}
git checkout ${MERGE_BRANCH}

# Find the commit on which the PR is based.
MERGE_BASE=$(git merge-base ${BASE_BRANCH} ${MERGE_BRANCH})
echo "Checking for formatting errors introduced since $MERGE_BASE"

# Do the checking. "eval" is used so that quotes (as inserted into $EXCLUDES
# above) are not interpreted as parts of file names.
eval git-clang-format --binary clang-format-10 $MERGE_BASE -- $EXCLUDES
git diff > formatted.diff
if [[ -s formatted.diff ]] ; then
  echo 'Formatting error! The following diff shows the required changes'
  echo 'Use the raw log to get a version of the diff that preserves spacing'
  cat formatted.diff
  exit 1
fi
echo 'No formatting errors found'
exit 0
