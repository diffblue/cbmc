# *******************************************************************
#
# Module: Gather data produced by test running framework
#
# Author: Daniel Poetzl
#
# *******************************************************************

"""
Data gathering framework

The framework gathers the data produced by a test running driver script and
produces a csv results table.

The framework needs to be instantiated in a driver script, which configures and
adds a number of data gathering and checking passes to run (for an example see
`drivers/rd_gather_data.py`). Passes are added via `add_pass()`, and are run on
the output files produced by the testing framework when `gather_data()` is
invoked. The directory that contains the output of the test running framework
can be specified via the argument `output_root`.

A data gathering or checking pass is a callable that gets the contents of a file
as an argument. The passes need to define the file to read via the member
variable `input_file`. A data gathering pass corresponds to a column in the csv
results table and needs to additionally define a member variable `column`. It
gives the name of the column that corresponds to the pass. Each call to a data
gathering pass produces one entry in the respective column.

Both data gathering and checking passes return a pair (bool, str). The first
column indicates whether to run subsequent passes, and the second component
gives the extracted data to write to the csv column. The second component is
ignored for checking passes (i.e., passes that do not have a `column` member
variable).

For examples of configurable passes see `CopyPass` and `ExtractPass` below.
"""

import argparse
import os
import re
import csv
import sys

# Config
_output_root = ''
_output_file = ''
_progress = False

_passes = []

#
# Passes
#

class GatherDataPassException(Exception):
  pass


class CopyPass:
  def __init__(self, input_file, column):
    self.input_file = input_file
    self.column = column

  def __call__(self, s):
    return True, s.strip()


class ExtractPass:
  def __init__(self, input_file, column, regex, group=0, fmt=lambda s: s):
    self.input_file = input_file
    self.column = column
    self.regex = re.compile(regex)
    self.group = group
    self.fmt = fmt

  def __call__(self, s):
    m = self.regex.search(s)
    if m:
      return True, self.fmt(m.group(self.group))

    return True, self.fmt('')


class CheckPass:
  def __init__(self, input_file, regex=None, check=lambda s: True):
    self.input_file = input_file
    if regex:
      self.regex = re.compile(regex)
    else:
      self.regex = None
    self.check = check

  def __call__(self, s):
    if self.regex:
      m = self.regex.search(s)
      if not m:
        return False, ''

    return self.check(s), ''


class ProcessPass:
  def __init__(self, input_file, column, f=lambda s: s):
    self.input_file = input_file
    self.column = column
    self.f = f

  def __call__(self, s):
    return True, self.f(s)


def validate_pass(p):
  return hasattr(p, 'input_file')

#
# Helpers
#

def fatal(msg):
  print(msg, file=sys.stderr)
  sys.exit(1)


def progress(msg='', end='\n'):
  if _progress:
    print(msg, end=end, flush=True)

#
# Interface
#

_setup_done = False


def setup_arg_parser():
  parser = argparse.ArgumentParser(description='Gather data')
  parser.add_argument('--output-root', default='output_root')
  parser.add_argument('--output-file', default='results.csv')
  parser.add_argument('--progress', action='store_true')
  return parser


def setup(parser=None):
  """Set up the data gathering framework and parse arguments"""
  global _output_root
  global _output_file
  global _progress
  global _setup_done

  if not parser:
    parser = setup_arg_parser()

  args = parser.parse_args()

  _output_root = os.path.abspath(args.output_root)
  if not os.path.isdir(_output_root):
    fatal('Directory `' + _output_root + '` does not exist')

  _output_file = os.path.abspath(args.output_file)

  if os.path.exists(_output_file) and not os.access(_output_file, os.W_OK):
    fatal('Output file `' + _output_file + '` not writable')

  _progress = args.progress
  _setup_done = True

  return args


def add_pass(p):
  """Add a data gathering pass to be run"""
  global _passes
  assert _setup_done

  assert validate_pass(p)
  _passes.append(p)


def gather_data():
  """Run all added data gathering passes"""
  assert _setup_done
  assert _passes

  records = []

  worklist = [_output_root]

  progress('Starting exploration')
  file_counter = 0

  while worklist:
    d = worklist.pop()
    entries = [os.path.join(d, entry) for entry in os.listdir(d)]
    leaf = True
    for entry in entries:
      if os.path.isdir(entry):
        leaf = False
        worklist.append(entry)
    if leaf:
      file_counter += 1
      progress('File {:<7} '.format(file_counter), end='')

      rp = os.path.relpath(d, _output_root)
      records.append([rp])
      record = records[-1]

      cwd = os.getcwd()
      assert os.path.isabs(d)
      os.chdir(d)

      complete_record = False

      for p in _passes:
        gathers_data = hasattr(p, 'column')

        if complete_record:
          if gathers_data:   
            record.append('-')
          continue

        filename = os.path.join(d, p.input_file)

        if os.path.exists(filename):
          f = open(filename)
          s = f.read()
          f.close()
          b, r = p(s)
          assert '\n' not in r
          if gathers_data:
            if not r:
              r = '-'
            record.append(r)
          if not b:
            complete_record = True
            continue
        elif gathers_data:
          record.append('-')

        progress('#', end='')

      progress()
      os.chdir(cwd)

  progress('Writing result table')

  f = open(_output_file, 'w')
  writer = csv.writer(f)
  if records:
    heading = ['test']
    for p in _passes:
      if hasattr(p, 'column'):
        heading.append(p.column)
    writer.writerow(heading)
  for record in records:
    writer.writerow(record)
  f.close()

