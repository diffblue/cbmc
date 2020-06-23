#!/bin/bash

set -x
set -e
goto_cc="$1"
goto_harness="$2"
cbmc="$3"
goto_harness_args="${@:4:$#-4}"

source_dir="$(pwd)"
target_dir="$(mktemp -d)"

# Compiling
for file in "$source_dir"/*.c; do
  file_name="$(basename "$file")"
  "$goto_cc" -c "$file" -o "$target_dir"/"${file_name%.c}.o"
done

# Linking

main_exe="$target_dir/main.gb"
"$goto_cc" "$target_dir"/*.o -o "$main_exe"

harness_out_file="$target_dir/harness.c"
"$goto_harness" "$main_exe" "$harness_out_file" --harness-function-name harness $goto_harness_args
cat "$harness_out_file"
"$cbmc" "$main_exe" "$harness_out_file" --function harness

