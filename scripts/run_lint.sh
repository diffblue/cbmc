#!/bin/bash

set -e

if [[ "$#" -ne 2 ]]
then
    echo "Script for running the CPP linter only on modified lines."
    echo "Requires two arguments the start and the end"
    echo "start - a git reference that marks the first commit whose changes to consider"
    echo "end - a git reference that marks the last commit whose changes to consider"

    exit 1
fi

if ! [[ -e scripts/cpplint.py ]]
then
  echo "Lint script could not be found in the scripts directory"
  echo "Ensure cpplint.py is inside the scripts directory then run again"
  exit 1
fi

git_start=$1
git_end=$2

# Get the list of files that have changed
diff_files=`git diff --name-only $git_start $git_end`

# Build a filter that will filter the blame output
# to only include lines that come from one of the relevant_commits
# We do this by making the blame tool output the same hash for all
# lines that are too old.
blame_grep_filter=`git rev-parse "$git_start"`

# Build a regex for finding the line number of a given line inside blame
# First matches the 40 digit hash of the commi
# Then match an arbitary length number that represents the line in the original file
# Finally matches (and groups) another arbitary length digit which is the
# line in the final file
regex="[0-9a-f]{40} [0-9]+ ([0-9]+)"

# We only split on lines or otherwise the git  blame output is nonsense
IFS=$'\n'

are_errors=0

for file in $diff_files; do
  # If the file has been deleted we don't want to run the linter on it
  if ! [[ -e $file ]]
  then
    continue
  fi

  # We build another grep filter the output of the linting script
  lint_grep_filter="^("

  # Include line 0 errors (e.g. copyright)
  lint_grep_filter+=$file
  lint_grep_filter+=":0"

  # We first filter only the lines that start with a commit hash
  # Then we filter out the ones that come from the start commit
  modified_lines=`git blame $git_start..$git_end --line-porcelain $file | grep -E "^[0-9a-f]{40}" | { grep -v "$blame_grep_filter" || true; }`

  # For each modified line we find the line number
  for line in $modified_lines; do

    # Use the above regex to match the line number
    if [[ $line =~ $regex ]]
    then
      # Some bash magic to get the first group from the regex (the line number)
      LINENUM="${BASH_REMATCH[1]}"

      # The format from the linting script is filepath:linenum: [error type]
      # So we build the first bit to filter out relevant lines
      LINE_FILTER=$file:$LINENUM

      # Add the line filter on to the grep expression as we want
      # lines that match any of the line filters
      lint_grep_filter+="|"
      lint_grep_filter+=$LINE_FILTER
    fi
  done

  # Add the closing bracket
  lint_grep_filter+=")"

  # Run the linting script and filter by the filter we've build
  # of all the modified lines
  # The errors from the linter go to STDERR so must be redirected to STDOUT
  result=`python scripts/cpplint.py $file 2>&1 | { grep -E "$lint_grep_filter" || true; }`

  # Providing some errors were relevant we print them out
  if [ "$result" ]
  then
    are_errors=1
    (>&2 echo "$result")
  fi
done

unset IFS

# Return an error code if errors are found
exit $are_errors
