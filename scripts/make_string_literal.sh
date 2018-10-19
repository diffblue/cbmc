#!/usr/bin/sh
#
# Turn an entire file into a single C++ literal raw string, so that you can
# assign it to a variable at compile time by doing
#
#       const std::string my_string =
#     #include "my-file.c"
#       ;
#
# Usage: the file argv[2] is written to argv[3], but prepended with the string
#
#   R"argv[1](
#
# and appended with the string
#
#   )argv[1]"
#
# No newlines are inserted after the beginning delimiter so that the line
# numbers of the output file are the same as the input.
#
# Author: Kareem Khazem

if [ "$#" != 3 ]; then
  >&2 echo "make_string_literal.sh: error (got $# arguments, expected 3)"
  >&2 echo "Usage: make_string_literal.sh DELIMITER INPUT_FILE OUTPUT_FILE"
  exit 1
fi

if [ ! -f "$2" ]; then
  >&2 echo "make_string_literal.sh: error (file '$2' not found)"
  >&2 echo "Usage: make_string_literal.sh DELIMITER INPUT_FILE OUTPUT_FILE"
  exit 1
fi

printf "" > "$3"
{
  printf "R\"%s(" "$1"
  cat "$2"
  echo ")$1\""
} >> "$3"
