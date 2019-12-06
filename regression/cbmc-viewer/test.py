#!/usr/bin/env python3
"""Regession testing of CBMC-viewer.

This script runs cbmc-viewer on examples in the pass and fail
directories, and compares the results with expected results.  These
tests are implemented as a python script to guard against reasonable
changes to cbmc that would cause a simple textual diff of the html
output to fail.  An example is a change to cbmc that causes cbmc to
generate a different trace.  This script parses the html and compares
just the shape of the html.
"""

#pylint: disable=missing-docstring,invalid-name

import argparse
from   glob    import glob                # file name expansion
import logging                            # setup log files
import os                                 # get unix
import subprocess                         # get subprocess management
import textwrap
from   lxml    import etree               # parse HTML files


def epilog():
    return textwrap.dedent("""\
        This program runs cbmc-viewer on several test programs to
        generate a HTML report of CBMC's model checking, property
        checking, and coverage computation. It checks that the HTML
        output has the expected shape, ensuring that changes to CBMC's
        output do not break report generation.

        Tests are in subdirectories of the directories `pass' and
        `fail'. This program considers a directory to be a test if it
        contains a `cbmc-args' file. These files should contain
        arguments to CBMC, one per line.

        Test directories should contain a `compare' directory,
        containing the HTML files that cbmc-viewer is expected to emit.
        test.py will run cbmc-viewer and write the output to a `html'
        directory in each of the test directories, and then compare the
        output of `html' and `compare'.

        This program will write progress to stderr, and more detailed
        information to test.log. Passing --verbose will send the more
        detailed output to stderr as well as test.log.
    """)


def compareElements(e1, e2, expected):
    """Compare all elements from the given lxml.etree objects."""

    if expected == "fail":
        log_error = logging.debug
    elif expected == "pass":
        log_error = logging.error

    if e1.tag != e2.tag:
        log_error("Tags e1.tag and e2.tag differ.")
        log_error("e1.tag: %s", e1.tag)
        log_error("e2.tag: %s", e2.tag)
        return False
    if e1.text != e2.text: # Only considered as warnings, because they might differ
        logging.debug("Texts e1.text and e2.text differ.")
        logging.debug("e1.text: %s", e1.text.strip())
        logging.debug("e2.text: %s", e2.text.strip())
    if e1.tail != e2.tail:
        log_error("Tails e1.tail and e2.tail differ.")
        log_error("e1.tail: %s", e1.tail)
        log_error("e2.tail: %s", e2.tail)
        return False
    if e1.attrib != e2.attrib: # Only considered as warnings, because they might differ
        logging.debug("Attributes e1.attrib and e2.attrib differ.")
        logging.debug("e1.attrib: %s", e1.attrib)
        logging.debug("e2.attrib: %s", e2.attrib)
    if len(e1) != len(e2):
        log_error("Lengths of e1 and e2 differ.")
        log_error("e1: %d", len(e1))
        log_error("e2: %d", len(e2))
        return False
    return all(compareElements(c1, c2, expected) for c1, c2 in zip(e1, e2))


def treeDiff(expected):
    """Perform a structural diff to validate the generated HTML report."""

    try:
        parser = etree.HTMLParser()
        generateReportTree = etree.parse('html/index.html', parser)
        correctReportTree = etree.parse('compare/index.html', parser)
        return compareElements(
            generateReportTree.getroot(), correctReportTree.getroot(), expected)
    except OSError:
        logging.error("Unable to compare generated report with expected report")
        logging.error("files in cwd '%s': [", os.getcwd())
        for root, _, files in os.walk("."):
            for name in files:
                logging.error("  %s", os.path.join(root, name))
        logging.error("]")
        exit(1)

def textualDiff():
    """Perform a textual diff to validate the generated HTML report."""

    diff_file = open("diff.log", "w")
    cmd = "diff -r compare html/"
    res = subprocess.Popen(cmd, stdout=diff_file, shell=True)
    _, error = res.communicate()
    if error:
        logging.error("Command '%s' failed", cmd)

    return os.stat("diff.log").st_size == 0


def flatten_command_list(commands):
    ret = []
    for command in commands:
        tmp = []
        for word in command["command"]:
            if isinstance(word, str):
                tmp.append(word)
            elif isinstance(word, list):
                tmp.extend(word)
            else:
                logging.error("Command '%s' has word '%s' with incorrect "
                              "type '%s'", command, word, type(word))
                exit(1)

        new_command = dict(command)
        new_command["command"] = tmp
        for field in ["stdout", "fail-ok"]:
            if field not in new_command:
                new_command[field] = None

        ret.append(new_command)

    return ret


def generateReport(options):
    """Generate the HTML report with CBMC-viewer."""

    _commands = [{

        "command": ["goto-cc", glob("*.c"), "-o", "source.goto"],
    }, {

        "command": ["goto-instrument", "source.goto", "proofs.goto"],
    }, {

        "command": ["cbmc", "proofs.goto", options, "--trace"],
        "fail-ok": True,
        "stdout": "cbmc.log",
    }, {

        "command": [
            "cbmc", "proofs.goto", options, "--show-properties", "--xml-ui"
        ],
        "fail-ok": True,
        "stdout": "property.xml",
    }, {

        "command": [
            "cbmc", "proofs.goto",
            [o for o in options if o != "--unwinding-assertions"],
            "--cover", "location", "--xml-ui",
        ],
        "fail-ok": True,
        "stdout": "coverage.xml",
    }, {

        "command": [
            "cbmc-viewer",
            "--goto", "proofs.goto",
            "--srcdir", os.getcwd(),
            "--blddir", os.getcwd(),
            "--htmldir", "html",
            "--result", "cbmc.log",
            "--property", "property.xml",
            "--block", "coverage.xml",
            "--json-summary", "summary.json",
        ]
    }]
    commands = flatten_command_list(_commands)

    for command in commands:
        if command["stdout"] is not None:
            handle = open(command["stdout"], "w")
        else:
            handle = subprocess.DEVNULL

        try:
            logging.debug(
                "$ %s%s", " ".join(command["command"]),
                ("" if command["stdout"] is None else (" > %s" % command["stdout"])))
            proc = subprocess.run(command["command"],
                                  stdout=handle,
                                  stderr=subprocess.PIPE,
                                  universal_newlines=True)
        except FileNotFoundError:
            logging.error("Failed to run command '%s' in directory %s.",
                          " ".join(command["command"]), os.getcwd())
            logging.error("Please ensure that '%s' is on your $PATH",
                          command["command"][0])
            exit(1)

        if proc.returncode and not command["fail-ok"]:
            logging.error(textwrap.dedent("""\
                    Failed to run command '%s' in directory %s.
                    Output:
                    ---
                    %s
                    ---
                    end of command output"""),
                          " ".join(command["command"]), os.getcwd(), proc.stderr)
            exit(1)


def all_tests():
    """Return pairs of test directories and expected results"""
    for expected in ["pass", "fail"]:
        for root, _, fyles in os.walk(expected):
            if "cbmc-args" in fyles:
                yield (root, expected)


def set_up_loggers(args):
    logging.getLogger().setLevel(logging.DEBUG)

    stdout_handler = logging.StreamHandler()
    stdout_handler.setLevel(logging.DEBUG if args.verbose else logging.INFO)
    stdout_handler.setFormatter(
        logging.Formatter(fmt="%(message)s"))
    logging.getLogger().addHandler(stdout_handler)

    file_handler = logging.FileHandler("test.log", mode="w")
    file_handler.setLevel(logging.DEBUG)
    file_handler.setFormatter(
        logging.Formatter(fmt="%(message)s"))
    logging.getLogger().addHandler(file_handler)


def main():
    """ Regression script.

    Go through each test case, generate its report,
    and compare it against a previous correct report.
    """

    parser = argparse.ArgumentParser(
        epilog=epilog(), formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    set_up_loggers(args)

    testdir = os.getcwd()
    total_tests = len(next(os.walk(testdir))[1])
    failed_results = 0

    for test, expected in all_tests():
        options = []
        with open(os.path.join(test, "cbmc-args"), "r") as options_file:
            for option in options_file:
                options.append(option.strip())

        os.chdir(test)
        generateReport(options)
        if treeDiff(expected) == (expected == "pass"):
            logging.info('[OK] %s', test)
        else:
            logging.error('[FAILED]')
            failed_results += 1

        os.chdir(testdir)

    if failed_results == 0:
        logging.info('All tests were successful')
        exit(0)

    logging.error('%d of %d %s tests failed', failed_results, total_tests,
                  ('test' if total_tests == 1 else 'tests'))
    exit(1)


if __name__ == '__main__':
    main()
