#!/usr/bin/env python3

"""
Gather benchmarking data produced by `rd_run_test.py` in a csv table

Usage:
./rd_gather_data.py <output_root> <output_file>

<output_root>: root of directory tree to which `rd_run_test.py` wrote its output
<output_file>: file to write csv table to
"""

import gather_data as gd

def _main():
  gd.setup()

  fn = 'run_pass.data'

  p = gd.ExtractPass(fn, 'timeout', r'Timeout: (.*)', 1)
  gd.add_pass(p)

  p = gd.ExtractPass(fn, 'user time', r'User time: (.*)', 1)
  gd.add_pass(p)

  p = gd.ExtractPass(fn, 'sys time', r'Sys time: (.*)', 1)
  gd.add_pass(p)

  p = gd.ExtractPass(fn, 'real time', r'Real time: (.*)', 1)
  gd.add_pass(p)

  p = gd.ExtractPass(fn, 'maximum resident set size',
    r'Maximum resident set size: : (.*)', 1)
  gd.add_pass(p)

  p = gd.ExtractPass(fn, 'exit code', r'Exit code: (.*)', 1)
  gd.add_pass(p)

  gd.gather_data()


if __name__ == '__main__':
  _main()
