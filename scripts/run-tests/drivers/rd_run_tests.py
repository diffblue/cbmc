#!/usr/bin/env python3

"""
Benchmark reaching definitions analysis

Usage:
./rd_run_test.py <input_file> <analysis_root> <output_root>

<input_file>: file that lists the goto binaries/archives to analyse
<analysis_root>: directory into which all goto binaries are put before analysis
<output_root>: directory into which all analysis output files are put

"""

import run_tests as rt

def _main():
  rt.setup()

  # Check that file is a goto binary
  cmd = ['goto-analyzer', '--list-goto-functions']
  p = rt.CheckPass(cmd, retcode=lambda r: r == 0)
  rt.add_pass(p)

  # Check that goto binary has an entry point
  cmd = ['goto-analyzer' , '--show-goto-functions']
  p = rt.CheckPass(cmd, regex_stdout=r'__CPROVER__start')
  rt.add_pass(p)

  # Run analysis
  cmd = ['goto-analyzer', '--reaching-definitions', '--show']
  p = rt.RunPass(cmd, timeout=1800)
  rt.add_pass(p)

  rt.test()


if __name__ == '__main__':
  _main()
