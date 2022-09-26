#!/usr/bin/env python3
import argparse
import logging
import subprocess
import os
import re

def create_parser(options=None, description=None):
    """Create a parser for command line arguments."""

    options = options or []
    description = description or ""

    flags = [option.get('flag') for option in options]
    if '--verbose' not in flags:
        options.append({'flag': '--verbose', 'action': 'store_true', 'help': 'Verbose output'})
    if '--debug' not in flags:
        options.append({'flag': '--debug', 'action': 'store_true', 'help': 'Debug output'})

    parser = argparse.ArgumentParser(description=description)
    for option in options:
        flag = option.pop('flag')
        parser.add_argument(flag, **option)
    return parser

def configure_logging(args):
    """Configure logging level based on command line arguments."""

    # Logging is configured by first invocation of basicConfig
    fmt = '%(levelname)s: %(message)s'
    if args.debug:
        logging.basicConfig(level=logging.DEBUG, format=fmt)
        return
    if args.verbose:
        logging.basicConfig(level=logging.INFO, format=fmt)
        return
    logging.basicConfig(format=fmt)

def parse_arguments():

    options = [
        {'flag': '--pandoc-write',
         'default': 'markdown_phpextra',
         'help': 'pandoc --write option'},
        {'flag': '--pandoc-wrap',
         'default': 'none',
         'help': 'pandoc --auto option'},
        {'flag': 'file',
         'nargs': '*',
         'help': 'markdown files'},
    ]
    return create_parser(options, "Prepare markdown for doxygen").parse_args()


def pandoc(path, pandoc_write, pandoc_wrap, pandoc_filter=None):
    args = {
        '--write': pandoc_write,
        '--wrap', pandoc_wrap
    }
    if pandoc_filter:
        args['--filter'] = Path(pandoc_filter).resolve()


    lines = subprocess.run(['pandoc', **args, path],
                           check=True,
                           text=True,
                           capture_output=True).stdout.splitlines()
    return [patch_code_block(line) for line in lines]

################################################################

def test_patch_code_block():
    assert patch_code_block("``` c") == "```c"
    assert patch_code_block("``` sh") == "```sh"
    assert patch_code_block("~~~ c") == "~~~c"
    assert patch_code_block("~~~ sh") == "~~~sh"
    assert patch_code_block("```c") == "```c"
    assert patch_code_block("```   ") == "```  "

def test_patch_link_target():
    assert patch_link_target("../../helpful/cow/") == "helpful-cow.md"
    assert patch_link_target("helpful/cow") == "helpful-cow.md"
    assert patch_link_target("helpful/cow/") == "helpful-cow.md"
    assert patch_link_target("helpful-cow/") == "helpful-cow.md"

def test_patch_link():
    assert patch_link("[a](../../helpful/cow/)") == "[a](helpful-cow.md)"
    assert patch_link("[a](helpful/cow)") == "[a](helpful-cow.md)"
    assert patch_link("[a](helpful/cow/)") == "[a](helpful-cow.md)"
    assert patch_link("[a](helpful-cow/)") == "[a](helpful-cow.md)"

def test_patch_links():
    assert patch_links("a b [a](../../helpful/cow/) x [a](../../helpful/cow/)") == "a b [a](helpful-cow.md) x [a](helpful-cow.md)"

################################################################

def main():
    args = parse_arguments()
    configure_logging(args)

    for path in args.file:
        lines = pandoc(path, args.pandoc_write, args.pandoc_wrap)
        lines = [patch_links(line) for line in lines]
        for line in lines:
            print(line)

if __name__ == "__main__":
    main()
