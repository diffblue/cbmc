#!/usr/bin/env python3

import os
import sys

sys.path.append(os.path.dirname(sys.path[0]))

import run_tests as rt

def _main():
  parser = rt.setup_arg_parser()
  parser.add_argument('--test', default=1, type=int)
  args = rt.setup(parser)

  if args.test == 1:
    cmd = ['stress', '-m', '1', '--vm-bytes', '4000000000', '--vm-hang', '1',
      '-t', '30']

    rt.add_pass(rt.RunPass(cmd, 'one', ignore_file=True))
    rt.add_pass(rt.RunPass(cmd, 'two', timeout=5, ignore_file=True))
  
    cmd = ['stress', '-c', '1', '-t', '10']
  
    rt.add_pass(rt.RunPass(cmd, 'three', ignore_file=True))
    rt.add_pass(rt.RunPass(cmd, 'four', timeout=5, ignore_file=True))
  elif args.test == 2:
    rt.add_pass(rt.FalsePass())
  else:
    assert False

  rt.test()


if __name__ == '__main__':
  _main()
