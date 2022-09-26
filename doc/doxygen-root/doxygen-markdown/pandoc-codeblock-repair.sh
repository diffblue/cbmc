#!/bin/sh

# This script strips spaces from syntax highlighting for code blocks
# in markdown documents.

# Pandoc outputs ``` c and ~~~ c but and doxygen expects ```c and ~~~c.
# Pandoc ouputs leading spaces before ``` and ~~~ when the code block is
# part of a list item.

sed 's/^\( *```\) */\1/' | sed 's/^\( *~~~\) */\1/'
