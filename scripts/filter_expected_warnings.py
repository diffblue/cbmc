#!/usr/bin/env python
"""Script to filter out old warnings from doxygen."""

import sys
import re


class DoxygenWarning(object):
    """Doxygen warning class."""

    def __init__(self, firstline, filename, warning):
        self.firstline = firstline
        self.filename = filename
        self.warning = warning
        self.otherlines = []

    def equals_ignoring_path_and_line_number(self, other):
        """Return true if warnings have same filename and warning message."""
        if self.filename != other.filename:
            return False
        if self.warning != other.warning:
            return False
        return self.otherlines == other.otherlines

    def print_with_prefix(self, prefix):
        print(prefix + self.firstline)
        for line in self.otherlines:
            print(prefix + '  ' + line)


class WarningsList(object):
    """List of Doxygen warnings."""

    def __init__(self, all_lines):
        """Create a list of the warnings in this file."""
        self.warnings_list = []
        current = None

        warning_start_expr = re.compile(r'[^:]+/([^:/]+):\d+: (warning.*$)')

        for line in all_lines:
            if line.isspace():
                continue

            # Allow comments in the list of expected warnings.
            if line.startswith('#'):
                continue

            matched = warning_start_expr.match(line)
            if matched:
                filename = matched.group(1)
                warning = matched.group(2)
                current = DoxygenWarning(line.strip(), filename, warning)
                self.warnings_list.append(current)
            elif line.startswith('  '):
                current.otherlines.append(line.strip())
            else:
                # Assuming all warnings are of the form [path:line: warning:...]
                # (and the warnings about too many nodes have been filtered out).
                print('Error filtering warnings: Unexpected input format.')
                print('  Input:' + line)

    def contains(self, warning):
        """Check if a similar warning is in this list."""
        for other in self.warnings_list:
            if warning.equals_ignoring_path_and_line_number(other):
                return True
        return False

    def print_warnings_not_in_other_list(self, other, prefix):
        """Check if this a subset of other, and print anything missing."""
        missing_element_found = False
        for warning in self.warnings_list:
            if not other.contains(warning):
                missing_element_found = True
                warning.print_with_prefix(prefix)
        return missing_element_found


def ignore_too_many_nodes(all_lines):
    """Filter out lines about graphs with too many nodes."""
    too_many_nodes_expr = re.compile(
        r'warning: Include(d by)? graph for .* not generated, too many nodes. '
        + r'Consider increasing DOT_GRAPH_MAX_NODES.')
    return [x for x in all_lines if not too_many_nodes_expr.match(x)]


def filter_expected_warnings(expected_warnings_path):
    """Filter lines from stdin and print to stdout."""
    with open(expected_warnings_path, "r") as warnings_file:
        expected_warnings = WarningsList(warnings_file.readlines())

    new_warnings = WarningsList(ignore_too_many_nodes(sys.stdin.readlines()))

    # print unexpected warnings
    unexpected_warning_found = new_warnings.print_warnings_not_in_other_list(
        expected_warnings, '')

    # print expected warnings which aren't found
    expected_warning_not_found = expected_warnings.print_warnings_not_in_other_list(
        new_warnings, '-')

    if expected_warning_not_found:
        print('NOTE: Warnings prefixed with \'-\' are expected ' +
              'warnings which weren\'t found.')
        print('      Please update the list of expected warnings.')

    return unexpected_warning_found or expected_warning_not_found


if __name__ == "__main__":

    if len(sys.argv) != 2:
        print('usage: filter_expected_warnings.py <expected_warnings_file>')
        print('(warnings from stdin are filtered and printed to stdout)')
        sys.exit(1)

    problem_found = filter_expected_warnings(sys.argv[1])
    sys.exit(1 if problem_found else 0)
