#!/bin/bash

set -e

script_folder=`dirname $0`
absolute_repository_root=`git rev-parse --show-toplevel`

if [[ "$#" -gt 2 ]]
then
    echo "Script for running the CPP linter only on modified lines. Arguments:"
    echo "target - a git reference to the branch we want to compare against (default: 'master')"
    echo "tip - a git reference to the commit with changes (default: current working tree)"
    exit 1
fi

if ! [[ -e $script_folder/cpplint.py ]]
then
  echo "Lint script could not be found in the $script_folder directory"
  echo "Ensure cpplint.py is inside the $script_folder directory then run again"
  exit 1
fi

if ! [[ -e $script_folder/filter_by_diff.py ]]
then
  echo "Filter script could not be found in the $script_folder directory"
  echo "Ensure filter_by_diff.py is inside the $script_folder directory then run again"
  exit 1
fi

if [[ "$#" -gt 0 ]]
then
    git_start=$1
else
    git_start="master"
fi

if [[ "$#" -gt 1 ]]
then
    git_end=$2
    git_merge_base_end=$2
else
    git_end=""
    git_merge_base_end="HEAD"
fi

git_start=`git merge-base $git_start $git_merge_base_end`

cleanup()
{
  rm -f $diff_file
}

trap cleanup EXIT

diff_file=`mktemp`

git diff $git_start $git_end > $diff_file

# Get the list of files that have changed
diff_files=`git diff --name-only $git_start $git_end`

for file in $diff_files; do
  file=$absolute_repository_root/$file
  # If the file has been deleted we don't want to run the linter on it
  if ! [[ -e $file ]]
  then
    continue
  fi

  # Run the linting script and filter:
  # The errors from the linter go to STDERR so must be redirected to STDOUT
  result=`$script_folder/cpplint.py $file 2>&1 >/dev/null | $script_folder/filter_by_diff.py $file $diff_file $absolute_repository_root`

  # Providing some errors were relevant we print them out
  if [ "$result" ]
  then
    are_errors=1
    (>&2 echo "$result")
  fi
done

# Return an error code if errors are found
exit $are_errors
