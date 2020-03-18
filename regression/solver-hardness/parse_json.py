#!/usr/bin/env python

import sys
import json

def main():
  with open(sys.argv[1], "r") as json_file:
    data = json.load(json_file)
  print ("Valid JSON File")
  print (json.dumps(data))

if __name__ == "__main__":
  main()
