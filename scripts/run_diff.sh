#!/bin/bash

set -e

script_folder=$(dirname "$0")
absolute_repository_root=$(git rev-parse --show-toplevel)
mode=$1
modes="CPPLINT"

if [[ "$#" -gt 3 ]]
then
  echo "Script for running a checker script only on modified lines. Arguments:"
  echo "mode - tool to run: $modes"
  echo "target - a git reference to the branch we want to compare against (default: 'master')"
  echo "tip - a git reference to the commit with changes (default: current working tree)"
  exit 1
fi

if ! [[ -e ${script_folder}/filter_by_lines.py ]]
then
  echo "Filter script could not be found in the $script_folder directory"
  echo "Ensure filter_by_lines.py is inside the $script_folder directory then run again"
  exit 1
fi

if [[ "$mode" == "CPPLINT" ]]
then
  if ! which iconv >/dev/null
  then
    echo "Couldn't find iconv in current path. Please install and try again"
    exit 1
  fi

  if ! [[ -e "${script_folder}/cpplint.py" ]]
  then
    echo "Lint script could not be found in the $script_folder directory"
    echo "Ensure cpplint.py is inside the $script_folder directory then run again"
    exit 1
  else
    cmd='${script_folder}/cpplint.py --filter=-whitespace/operators,-readability/identifier_spacing $file 2>&1 >/dev/null'
  fi
else
  echo "Mode $mode not recognized"
  echo "Possible values: $modes"
  exit 1
fi

if [[ "$#" -gt 1 ]]
then
    git_start=$2
else
    git_start="master"
fi

if [[ "$#" -gt 2 ]]
then
    git_end=$3
    git_merge_base_end=$3
else
    git_end=""
    git_merge_base_end="HEAD"
fi

git_start=$(git merge-base $git_start $git_merge_base_end)

cleanup()
{
  rm -f "$diff_file" "$added_lines_file"
}

trap cleanup EXIT

diff_file=$(mktemp)
added_lines_file=$(mktemp)

# Pass the output through iconv to remove any invalid UTF-8 (diff_to_added_lines.py will die otherwise)

git diff $git_start $git_end | iconv -t utf-8 -c > "$diff_file"

# Get the list of files that have changed, that end with lintable extensions
diff_files=$(git diff --name-only $git_start $git_end | grep "\.\(\(cpp\)\|\(hh\)\|\(cc\)\|h\)$" || true)

"${script_folder}/diff_to_added_lines.py" "$diff_file" "$absolute_repository_root" > "$added_lines_file"

for file in $diff_files; do
  file=$absolute_repository_root/$file
  # If the file has been deleted we don't want to run the linter on it
  if ! [[ -e $file ]]
  then
    continue
  fi

  # Run the linting script and filter:
  # The errors from the linter go to STDERR so must be redirected to STDOUT
  result=$(eval "${cmd}" | "${script_folder}/filter_by_lines.py" "$file" "$added_lines_file" "$absolute_repository_root")

  # Providing some errors were relevant we print them out
  if [ "$result" ]
  then
    are_errors=1
    (>&2 echo "$result")
  fi
done

# Return an error code if errors are found
exit $are_errors
