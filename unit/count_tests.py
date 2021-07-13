#!/usr/bin/env python3
#
# Count number of unit tests.
#

import argparse
import os
import sys


def tests_in_file(file_path):
    file_test_count = 0
    with open(file_path, "rt") as file:
        for line in file:
            if line.startswith("TEST_CASE"):
                file_test_count += 1
            if line.startswith("SCENARIO"):
                file_test_count += 1
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
