"""The results of cbmc-storm."""
from __future__ import print_function

from builtins import object
import re

# pylint: disable=line-too-long
# pylint: disable=too-many-instance-attributes
# pylint: disable=too-many-branches
# pylint: disable=too-many-statements

ERROR_HEADER = re.escape('*** ERRORS ***')
WARNING_HEADER = re.escape('*** WARNINGS ***')
NO_ERROR_HEADER = re.escape('***NO ERRORS WERE FOUND IN THE FOLLOWING NODES ***')
TIMED_OUT_HEADER = re.escape('**** CBMC TIMED OUT IN THE FOLLOWING NODES ***')
FAILED_HEADER = re.escape('**** CBMC FAILED TO RUN IN THE FOLLOWING NODES ***')

PROPERTY_HEADER = re.escape('Violated property')
TRACE_HEADER = "Trace for (.*):"


def clean(s):
    """Replace whitespace with a space and strip whitespace from ends."""
    return re.sub(r'\s+', ' ', s).strip()


class Storm(object):
    """The results reported by cbmc-storm."""

    def __init__(self, log):
        """Initialize the results from the cbmc-storm log file."""

        # Property attributes (init helper members)
        self.name = ""
        self.description = ""
        self.file = ""
        self.func = ""
        self.line = ""
        self.expr = ""
        self.error = True
        self.trace = ""

        # Maps a property name to property attributes
        self.property = {}

        self.no_errors = []
        self.cbmc_timed_out = []
        self.cbmc_failed = []

        try:
            fh = open(log, 'r')
        except IOError:
            print('Failed to open {} for reading.'.format(log))
            return

        # Property parsing states
        in_prop_desc = False
        in_prop_loc = False
        in_prop_formula = False
        in_trace = False

        in_no_errors = False
        in_cbmc_timed_out = False
        in_cbmc_failed = False

        for line in fh:
            line = clean(line)

            if re.match(ERROR_HEADER, line):
                self.insert_property()
                self.clear_property()
                self.error = True
                in_trace = False
                continue

            if re.match(WARNING_HEADER, line):
                self.insert_property()
                self.clear_property()
                self.error = False
                in_trace = False
                continue

            if re.match(NO_ERROR_HEADER, line):
                self.insert_property()
                self.clear_property()
                in_trace = False
                in_no_errors = False
                in_cbmc_timed_out = False
                in_cbmc_failed = False
                in_no_errors = True
                continue

            if re.match(TIMED_OUT_HEADER, line):
                self.insert_property()
                self.clear_property()
                in_trace = False
                in_no_errors = False
                in_cbmc_timed_out = False
                in_cbmc_failed = False
                in_cbmc_timed_out = True
                continue

            if re.match(FAILED_HEADER, line):
                self.insert_property()
                self.clear_property()
                in_trace = False
                in_no_errors = False
                in_cbmc_timed_out = False
                in_cbmc_failed = False
                in_cbmc_failed = True
                continue

            if re.match(PROPERTY_HEADER, line):
                self.insert_property()
                self.clear_property()
                in_prop_loc = True
                continue

            if in_prop_loc:
                self.file = ""
                self.func = ""
                self.line = ""
                match = re.match('file (.*) function (.*) line (.*)', line)
                if match:
                    self.file = match.group(1)
                    self.func = match.group(2)
                    self.line = match.group(3)
                in_prop_loc = False
                in_prop_desc = True
                continue

            if in_prop_desc:
                self.description = line
                in_prop_desc = False
                in_prop_formula = True
                continue

            if in_prop_formula:
                self.expr = line
                in_prop_formula = False
                continue

            if re.match(TRACE_HEADER, line):
                self.name = re.match(TRACE_HEADER, line).group(1)
                self.trace = line
                in_trace = True

            if in_trace:
                self.trace += line + '\n'

            if in_no_errors and line:
                self.no_errors.append(line)
                continue

            if in_cbmc_timed_out and line:
                self.cbmc_timed_out.append(line)
                continue

            if in_cbmc_failed and line:
                self.cbmc_failed.append(line)
                continue

        self.insert_property()
        self.clear_property()

    def insert_property(self):
        """Insert the property accumulator into the property list"""

        if self.name:
            self.property[self.name] = {
                'name': self.name,
                'desc': self.description,
                'file': self.file,
                'func': self.func,
                'line': self.line,
                'error': self.error,
                'expr': self.expr,
                'trace': self.trace
                }

    def clear_property(self):
        """Clear the property accumulator"""

        self.name = ""
        self.description = ""
        self.file = ""
        self.func = ""
        self.line = ""
        # self.error
        self.expr = ""
        self.trace = ""

################################################################
