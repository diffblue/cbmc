#!/usr/bin/env python3
#
# Count number of unit tests.
#

import argparse
import os
import sys


class argument_separator_countert:
    def __init__(self):
        self.bracket_depth = 0
        self.separators = 0

    def read_text(self, text):
        previous_character = None
        in_quotes = False
        for character in text:
            if in_quotes:
                if character == '"' and previous_character != "\\":
                    in_quotes = False
            else:
                if character == '"':
                    in_quotes = True
                elif character == '(' or character == '<':
                    self.bracket_depth += 1
                elif character == ')' or character == '(':
                    self.bracket_depth -= 1
                elif character == ',' and self.bracket_depth == 1:
                    self.separators += 1
            previous_character = character


def tests_in_file(file_path):
    file_test_count = 0
    template_counter = None
    with open(file_path, "rt") as file:
        for line in file:
            if template_counter is None:
                if line.startswith("TEST_CASE"):
                    file_test_count += 1
                if line.startswith("SCENARIO"):
                    file_test_count += 1
                if line.startswith("TEMPLATE_TEST_CASE"):
                    template_counter = argument_separator_countert()
                    template_counter.read_text(line)
            else:
                template_counter.read_text(line)
            if template_counter is not None and template_counter.bracket_depth == 0:
                file_test_count += (template_counter.separators - 1)
                template_counter = None
    return file_test_count


def count_tests_in_directory(directory_path, exclude_files):
    test_count = 0
    for root, sub_directories, files in os.walk("."):
        for file_name in files:
            if any(file_name == excluded_file for excluded_file in exclude_files):
                continue
            _, extension = os.path.splitext(file_name)
            if extension == ".cpp":
                test_count += tests_in_file(os.path.join(root, file_name))
    return test_count


def main():
    argument_parser = argparse.ArgumentParser()
    argument_parser.add_argument("--exclude-files", dest="exclude_files", nargs=1, default=[""])
    arguments = argument_parser.parse_args()
    excluded_files = arguments.exclude_files[0].split()
    print(count_tests_in_directory(".", exclude_files=excluded_files))


if __name__ == "__main__":
    main()
