"""CBMC results."""

import re


def clean(s):
    """Replace whitespace with a space and strip whitespace from ends."""
    return re.sub('\b+', ' ', s).strip()

################################################################

class Result:
    """CBMC results."""

    def __init__(self, log=""):
        """Initialize with results from output of cbmc."""

        # pylint: disable=too-many-locals

        self.result = {}
        self.success = []
        self.failure = []
        self.error = {}
        self.warning = {}

        if log == "":
            return

        try:
            logfh = open(log, "r")
        except IOError as e:
            print(("Can't read cbmc results: "
                   "Unable to open {} for reading: {}")
                  .format(log, e.strerror))
            return

        # Regular expressions used to parse the results output by cbmc
        timestamp_re = r'(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}.\d{6})'
        results_re = r'\[([^]]*)\].*(SUCCESS|FAILURE)'
        match_re = '({} )?{}'.format(timestamp_re, results_re)

        # Constants for selecting matches with match.group(n)
        #timestamp_group = 2
        name_group = 3
        result_group = 4

        regexp = re.compile(match_re)

        found = False
        for line in logfh:
            line = clean(line)
            if line == "** Results:":
                found = True
                continue
            if not found:
                continue

            match = regexp.match(line)
            if not match:
                continue

            name = match.group(name_group)
            result = match.group(result_group)
            self.result[name] = result
            if result == "SUCCESS":
                self.success.append(name)
            if result == "FAILURE":
                self.failure.append(name)
                self.error[name] = True

    def lookup(self, name):
        """Lookup result by name."""
        return self.result.get(name)

    def failures(self):
        """Return failed properties."""
        return self.failure

    def successes(self):
        """Return successful properties."""
        return self.success

################################################################
