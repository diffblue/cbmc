#!/usr/bin/env sh

# This script can be used in conjunction with git and the doc-reformatting
# script (reformat_docs.py) to facilitate automatic rebases/merges spanning the
# transition to Doxygen-style comments.
# Usage information: https://svn.cprover.org/wiki/doku.php?id=doxygen

script_dir="$(dirname "$0")"

python "${script_dir}/reformat_docs.py" "$1" -i
python "${script_dir}/reformat_docs.py" "$2" -i
python "${script_dir}/reformat_docs.py" "$3" -i
git merge-file "$1" "$2" "$3"
