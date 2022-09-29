#!/usr/bin/env python3

import subprocess
import sys
import re


class Options:
    def __init__(self):
        self.cmd_binary = sys.argv[1]
        self.test_name = sys.argv[2]
        self.cmd_options = sys.argv[3:]
        self.outfile = self.test_name + "-out-file.out"
        self.outfile_rules = self.test_name + "-out-file-rules.txt"

    def __str__(self):
        return """
  cmd_binary: {},
  test_name: {},
  cmd_options: {},
  outfile: {},
  outfile_rules: {},
        """.format(self.cmd_binary,
                   self.test_name,
                   self.cmd_options,
                   self.outfile,
                   self.outfile_rules)


def try_compile_regex(regex_content):
    try:
        return re.compile(regex_content)
    except re.error:
        print("Bad regex: {}".format(regex_content))
        raise


def check_outfile(options):
    with open(options.outfile) as outfile_f:
        with open(options.outfile_rules) as outfile_rules_f:
            unprocessed_outfile = outfile_f.readlines()
            outfile_rules = [try_compile_regex(c) for c in outfile_rules_f.readlines()]
            for rule in outfile_rules:
                found = False
                while not found:
                    if len(unprocessed_outfile) == 0:
                        return False
                    match = rule.match(unprocessed_outfile[0])
                    found = match is not None
                    unprocessed_outfile = unprocessed_outfile[1:]
    return True


def main():
    options = Options()
    cmd_options = [options.outfile if item == '%out-file-name%' else item for item in
                   options.cmd_options]
    cmd_line = [options.cmd_binary] + cmd_options
    print("Running: ", cmd_line)
    subprocess.run(cmd_line)
    print("\n--- Checking outfiles ---")
    if check_outfile(options):
        print("Output file matches.")
        sys.exit(0)
    else:
        print("Output file does not match.")
        sys.exit(1)


if __name__ == "__main__":
    main()
