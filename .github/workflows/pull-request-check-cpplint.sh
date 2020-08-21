#!/bin/bash

# Stop on errors
set -e

# Log information about the run of this check.
echo "Pull request's base branch is: ${BASE_BRANCH}"
echo "Pull request's merge branch is: ${MERGE_BRANCH}"
echo "Pull request's source branch is: ${GITHUB_HEAD_REF}"

# The checkout action leaves us in detatched head state. The following line
# names the checked out commit, for simpler reference later.
git checkout -b ${MERGE_BRANCH}

# Make sure we can refer to ${BASE_BRANCH} by name
git checkout ${BASE_BRANCH}
git checkout ${MERGE_BRANCH}

# Find the commit on which the PR is based.
MERGE_BASE=$(git merge-base ${BASE_BRANCH} ${MERGE_BRANCH})
echo "Checking standards of code touched since $MERGE_BASE"

# Do the checking.
./scripts/run_diff.sh CPPLINT $MERGE_BASE
