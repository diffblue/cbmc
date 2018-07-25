#!/usr/bin/env python3

import os
import sys

sys.path.append(os.path.dirname(sys.path[0]))

import gather_data as gd

def _main():
  gd.setup()
  gd.add_pass(gd.CopyPass('test1.txt', 'test1-a'))
  gd.add_pass(gd.CopyPass('test1.txt', 'test1-b'))
  gd.add_pass(gd.CopyPass('test2.txt', 'test2'))
  gd.gather_data()


if __name__ == '__main__':
  _main()
