#!/usr/bin/env python3

# Find regression tests that cover given source lines

import argparse
import os
import re
import subprocess
import sys

description =\
'''\
Find cbmc regression tests that cover given source lines

The program for which to analyse coverage needs to be built with gcc/g++/ld and
flag --coverage (or equivalent), and the gcov command needs to be available.

Example (assuming the script is invoked from the cbmc root directory):

find-covering-tests.py \\
  --directory regression/cbmc \\
  --command '../test.pl -c cbmc' \\
  --source-line 'src/cbmc_parse_options.cpp:322' \\
  --source-line 'src/goto_symex.cpp:53'

The invocation above determines the regression tests in regression/cbmc which
cover line 322 of file cbmc_parse_options.cpp or line 53 of file goto_symex.cpp.
'''

def remove_existing_coverage_data(source_lines):
  source_files = [item[0] for item in source_lines]

  for filename in source_files:
    pre, ext = os.path.splitext(filename)
    gcda_file = pre + '.gcda'

    gcov_file = filename + '.gcov'

    try:
      os.remove(gcda_file)
      os.remove(gcov_file)
    except:
      pass


def parse_source_lines(source_lines):
  return [(item[0], int(item[1])) for item in
          map(lambda s: s.split(':'), source_lines)]


def is_covered_source_line(filename, line):
  if not os.path.isfile(filename):
    return False

  d = os.path.dirname(filename)
  b = os.path.basename(filename)
  subprocess.run(['gcov', b],
                 cwd=d, stdout=subprocess.DEVNULL,
                 stderr=subprocess.DEVNULL,
                 check=True)

  gcov_file = filename + '.gcov'
  if not os.path.isfile(gcov_file):
    return False

  f = open(gcov_file)
  s = f.read()
  f.close()

  mo = re.search('^\s*[1-9][0-9]*:\s+' + str(line) + ':', s, re.MULTILINE)
  return mo is not None


def get_covered_source_lines(source_lines):
  covered_source_lines = []

  for filename, line in source_lines:
    if is_covered_source_line(filename, line):
      covered_source_lines.append((filename, line))

  return covered_source_lines


def run(config):
  source_lines = parse_source_lines(config.source_line)

  dirs = filter(
    lambda entry: os.path.isdir(os.path.join(config.directory, entry)),
    os.listdir(config.directory))

  for d in dirs:
    remove_existing_coverage_data(source_lines)
    print('Running test ' + d)
    subprocess.run([config.command + ' ' + d],
                   cwd=config.directory,
                   shell=True,
                   stdout=subprocess.DEVNULL,
                   stderr=subprocess.DEVNULL,
                   check=True)
    
    covered_source_lines = get_covered_source_lines(source_lines)
    if covered_source_lines:
      print('  Covered source lines:')
      for filename, line in covered_source_lines:
        print('  ' + filename + ':' + str(line))
    else:
      print('  Does not cover any of the given source lines')


if __name__ == '__main__':

  parser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description=description)

  parser.add_argument(
    '--source-line',
    action='append',
    metavar='<filename>:<line>',
    required=True,
    help='source lines for which to determine which tests cover them, can be '
      'repeated')
  parser.add_argument('--command', required=True,
    help='regression test command, typically an invocation of test.pl')
  parser.add_argument('--directory', required=True,
    help='directory containing regression test directories')

  config = parser.parse_args()

  run(config)

