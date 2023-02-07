#!/bin/bash

set -euo pipefail

BINDIR=$(dirname $(realpath ${BASH_SOURCE[0]}))
FILES=$(find . -name '*.md')

# Append the last modified date to the end of every markdown file

echo
echo "Appending last modified dates to markdown files"
$BINDIR/append-last-modified-dates.py $FILES

# Doxygen parses incorrectly a link [what a link](what-a-link.md) that
# is broken over two lines.
# Doxygen requires that headings '# heading' have labels '{# heading}'
# for section linking to work.  The markdown extension "php Markdown
# Extra" supports section labels.
# Use pandoc to remove line breaks from paragraphs and to output a
# markdown extension with section labels.
# Note: Need to read markdown as markdown_phpextra and not default
# markdown to preserve doxygen pragmas like \ingroup.

# Bug: This is currently interacting badly with \dot in cprover markdown

# echo
# echo "Running pandoc over markdown files"
# for file in $FILES; do
#     echo $file
#     tmp=/tmp/${file%.*}1.md
#     mkdir -p $(dirname $tmp)
#     cp $file $tmp
#     pandoc --read=markdown_phpextra --write=markdown_phpextra --wrap=none $tmp | \
#         $BINDIR/pandoc-codeblock-repair.sh > $file
# done

echo
echo "Rendering mermaid diagrams"
FILES=$(grep --include=\*.md -rl . -e "\`\`\`mermaid")
for file in $FILES; do
    echo $file
    tmp=/tmp/${file%.*}2.md
    mkdir -p $(dirname $tmp)
    cp $file $tmp
    # Note that gfm is GitHub Flavour Markdown. The double \\ at the start of
    # lines is unescaped using sed in order to fix doxygen tags, which are
    # broken by pandoc.
    pandoc --read=gfm --write=gfm --wrap=none --filter=mermaid-filter $tmp |
        $BINDIR/pandoc-codeblock-repair.sh | sed 's/\\\\ref\s/\\ref /;s/^\\\\/\\/' > $file
done

cprovers=$(find . -name cprover-manual)
cprover=${cprovers[0]}

# Markdown files in cprover-manual have hierarchical links like
# ../../pretty/cow/ that refer to the markdown file pretty-cow.md.
# The site http://www.cprover.org/cprover-manual/ uses a javascript
# script running in the browser to serve up pages from the
# cprover-manual directory.  Use a pandoc filter to patch up the
# cprover-manual links before running doxygen.

echo
echo "Running pandoc filter over cprover-manual markdown files"
FILES=$(find $cprover -name '*.md')
for file in $FILES; do
    echo $file
    tmp=/tmp/${file%.*}3.md
    mkdir -p $(dirname $tmp)
    cp $file $tmp
    pandoc  --write=markdown_phpextra --wrap=none --filter=$BINDIR/pandoc-cprover-link-filter.py $tmp |
        $BINDIR/pandoc-codeblock-repair.sh > $file
done
