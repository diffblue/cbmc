#!/bin/bash

set -x
set -e
goto_cc="$1"
goto_harness="$2"
cbmc="$3"
is_windows=$4
goto_harness_args="${@:5:$#-5}"

cleanup()
{
  rm -rf "$target_dir"
}

trap cleanup EXIT

# create the temporary directory relative to the current directory, thus
# avoiding file names that start with a "/", which confuses goto-cl (Windows)
# when running in git-bash.
target_dir="$(TMPDIR=. mktemp -d)"

# Compiling
for file in *.c; do
  file_name="$(basename "$file")"
  if [[ "${is_windows}" == "true" ]]; then
    "$goto_cc" "/c" "$file" "/Fo$target_dir/${file_name%.c}.obj"
  else
    "$goto_cc" -c "$file" -o "$target_dir"/"${file_name%.c}.o"
  fi
done

# Linking

main_exe="$target_dir/main.gb"
if [[ "${is_windows}" == "true" ]]; then
  "$goto_cc" "$target_dir"/*.obj "/Fe$main_exe"
else
  "$goto_cc" "$target_dir"/*.o -o "$main_exe"
fi

harness_out_file="$target_dir/harness.c"
"$goto_harness" "$main_exe" "$harness_out_file" --harness-function-name harness $goto_harness_args
cat "$harness_out_file"
"$cbmc" "$main_exe" "$harness_out_file" --function harness

