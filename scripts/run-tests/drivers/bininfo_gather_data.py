#!/usr/bin/env python3

import re
import sys
import gather_data as gd

def _boolstr(s):
  assert type(s) is str
  return str(bool(s))


def _count_goto_functions(s):
  lines = s.splitlines()
  lines = filter(lambda l: l and 'Reading GOTO program' not in l, lines)
  n = len(list(lines))
  return str(n)


def _count_goto_instructions(s):
  l = re.findall(r'^\s+// [0-9]+', s, re.MULTILINE)
  return str(len(l))


def _main():
  gd.setup()

  exit_success = r'Exit code: 0'

  # Last modified time
  p = gd.CopyPass('get_modified_time_pass', 'mtime')
  gd.add_pass(p)

  # Size of file
  p = gd.CopyPass('get_size_pass', 'size')
  gd.add_pass(p)

  # Is a goto binary
  f = 'list_goto_functions.run_pass.data'
  p = gd.ExtractPass(f, 'goto binary', exit_success, fmt=_boolstr)
  gd.add_pass(p)
  p = gd.CheckPass(f, exit_success)
  gd.add_pass(p)

  # Number of goto functions
  p = gd.ProcessPass(
        'list_goto_functions.run_pass.stdout',
        'num goto functions',
        _count_goto_functions)
  gd.add_pass(p)

  # Effective lines of code
  p = gd.CheckPass('count_eloc.run_pass.data', exit_success)
  gd.add_pass(p)
  p = gd.ExtractPass(
        'count_eloc.run_pass.stdout',
        'effective lines of code',
        r'Effective lines of code: ([0-9]+)',
        1)
  gd.add_pass(p)

  # Has __CPROVER__start
  f = 'show_goto_functions.run_pass.stdout'
  p = gd.CheckPass('show_goto_functions.run_pass.data', exit_success)
  gd.add_pass(p)
  p = gd.ExtractPass(f,
        'has __CPROVER__start',
        r'__CPROVER__start',
        fmt=_boolstr)
  gd.add_pass(p)

  # Has _start
  p = gd.ExtractPass(f, 'has _start', r' _start', fmt=_boolstr)
  gd.add_pass(p)
  
  # Number of goto instructions
  p = gd.ProcessPass(f, 'num instructions', _count_goto_instructions)
  gd.add_pass(p)

  # Has concurrency
  p = gd.ExtractPass(
        f,
        'has concurrency',
        r'pthread_create|__CPROVER_async',
        fmt=_boolstr)
  gd.add_pass(p)

  gd.gather_data()


if __name__ == '__main__':
  _main()
