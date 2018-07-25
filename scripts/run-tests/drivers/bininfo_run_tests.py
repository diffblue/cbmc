#!/usr/bin/env python3

import os
import sys
import re
import datetime
import run_tests as rt

cbmc = 'cbmc'
gi = 'goto-instrument'
ga = 'goto-analyzer'


class GetSizePass:
  def __init__(self):
    self.output = 'get_size_pass'

  def __call__(self, f, output_file):
    assert os.path.exists(f)
    num_bytes = os.path.getsize(f)
    output_file.write(str(num_bytes))
    return True


class CheckSizePass:
  def __init__(self, max_bytes):
    self.max_bytes = max_bytes

  def __call__(self, f):
    assert os.path.exists(f)
    num_bytes = os.path.getsize(f)
    return num_bytes <= self.max_bytes


class GetModifiedTimePass:
  def __init__(self):
    self.output = 'get_modified_time_pass'

  def __call__(self, f, output_file):
    assert os.path.exists(f)
    n = os.path.getmtime(f)
    d = datetime.date.fromtimestamp(n)
    s = d.isoformat()
    output_file.write(s)
    return True


def _main():
  rt.setup()

  rt.add_pass(GetModifiedTimePass())

  rt.add_pass(GetSizePass())
  rt.add_pass(CheckSizePass(10 ** 8))

  cmd = [cbmc, '--list-goto-functions']
  p = rt.RunPass(cmd, 'list_goto_functions')
  rt.add_pass(p)
  p = rt.CheckPass(cmd, retcode=lambda r: r == 0)
  rt.add_pass(p)

  cmd = [gi, '--count-eloc']
  p = rt.RunPass(cmd, 'count_eloc')
  rt.add_pass(p)
  def f(s):
    m = re.search(r'Effective lines of code: ([0-9]+)', s)
    assert m
    i = int(m.group(1))
    return i <= 100000
  p = rt.CheckPass(cmd, check_stdout=f)
  rt.add_pass(p)

  cmd = [cbmc, '--show-goto-functions']
  p = rt.RunPass(cmd, 'show_goto_functions')
  rt.add_pass(p)

  rt.test()


if __name__ == '__main__':
  _main()
