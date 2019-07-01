#!/usr/bin/env python3
"""
Regession testing of CBMC-viewer.
"""

from __future__ import print_function     # get print function from Python 3

from   glob    import glob                # file name expansion
import logging                            # setup log files
import os                                 # get unix
import subprocess                         # get subprocess management
from   time    import time                # time functions
from   lxml    import etree               # parse HTML files

class bcolors:                            # get colors
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'


def compareElements(e1, e2):
    """Compare all elements from the given lxml.etree objects."""

    if e1.tag != e2.tag:
        logging.error("Tags e1.tag and e1.tag differ.")
        logging.error("e1.tag: %s", e1.tag)
        logging.error("e2.tag: %s", e2.tag)
        return False
    if e1.text != e2.text: # Only considered as warnings, because they might differ
        logging.warning("Texts e1.text and e1.text differ.")
        logging.warning("e1.text: %s", e1.text)
        logging.warning("e2.text: %s", e2.text)
    if e1.tail != e2.tail:
        logging.error("Tails e1.tail and e1.tail differ.")
        logging.error("e1.tail: %s", e1.tail)
        logging.error("e2.tail: %s", e2.tail)
        return False
    if e1.attrib != e2.attrib: # Only considered as warnings, because they might differ
        logging.warning("Attributes e1.attrib and e1.attrib differ.")
        logging.warning("e1.attrib: %s", e1.attrib)
        logging.warning("e2.attrib: %s", e2.attrib)
    if len(e1) != len(e2):
        logging.error("Lengths of e1 and e1 differ.")
        logging.error("e1: %d", len(e1))
        logging.error("e2: %d", len(e2))
        return False
    return all(compareElements(c1, c2) for c1, c2 in zip(e1, e2))


def treeDiff():
    """Perform a structural diff to validate the generated HTML report."""

    parser = etree.HTMLParser()
    generateReportTree = etree.parse('html/index.html', parser)
    correctReportTree = etree.parse('compare/html/index.html', parser)
    return compareElements(generateReportTree.getroot(), correctReportTree.getroot())


def textualDiff():
    """Perform a textual diff to validate the generated HTML report."""

    diff_file = open("diff.log", "w")
    cmd = "diff -r compare/html html/"
    subprocess.Popen(cmd, stdout=diff_file, shell=True)
    return os.stat("diff.log").st_size == 0


def generateReport(options):
    """Generate the HTML report with CBMC-viewer."""

    try:
        cmd = "goto-cc *.c -o source.goto"
        subprocess.call(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)

        cmd = "goto-instrument source.goto proofs.goto"
        subprocess.call(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)

        output_file = open("cbmc.log", "w")
        cmd = "cbmc proofs.goto " + options + " --trace"
        subprocess.Popen(cmd, stdout=output_file, stderr=subprocess.PIPE, shell=True)

        property_file = open("property.xml", "w")
        cmd = cmd.replace('--trace', '--show-properties --xml-ui')
        subprocess.Popen(cmd, stdout=property_file, stderr=subprocess.PIPE, shell=True)

        options.replace('--unwinding-assertions', '')
        coverage_file = open("coverage.xml", "w")
        cmd = cmd.replace("--unwinding-assertions --show-properties", "--cover location")
        subprocess.Popen(cmd, stdout=coverage_file, stderr=subprocess.PIPE, shell=True)

        cmd = "cbmc-viewer --goto proofs.goto --srcdir $PWD --blddir $PWD --htmldir html "
        cmd += "--result cbmc.log --property property.xml --block coverage.xml "
        cmd += "--json-summary summary.json > /dev/null 2>&1"
        subprocess.call(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    except OSError as err:
        logging.error("Can't run command '%s': %s", cmd, str(err))
        return


def main():
    """ Regression script.

    Go through each test case, generate its report,
    and compare it against a previous correct report.
    """

    logging.basicConfig(filename='test.log',
                        filemode='w',
                        format='%(name)s - %(levelname)s - %(message)s')

    testdir = "./"
    total_tests = len(next(os.walk(testdir))[1])
    failed_results = 0
    duration = 0

    print ('Loading')
    print (total_tests, ('test' if total_tests == 1 else 'tests') + ' found\n')

    for test in glob(testdir + '*/'):      # for all test cases
        print ('  Running ', os.path.basename(test), end='')

        options = open(test + '/test.desc', 'r').read()    # get CBMC flags
        options = options.replace("\n", "")

        os.chdir(test)
        start_time = time()
        generateReport(options)
        if treeDiff():
            print (' [' + bcolors.OKGREEN + 'OK' + bcolors.ENDC + ']', end='')
        else:
            print(' [' + bcolors.FAIL + 'FAILED' + bcolors.ENDC + ']', end='')
            failed_results += 1
        print(" (%s seconds)" %  round(time() - start_time, 2))
        duration += round(time() - start_time, 2)
        os.chdir('../.')

    print ('\n  Duration: %s seconds\n' % duration)

    if failed_results == 0:
        print (bcolors.OKGREEN + 'All tests were successful' + bcolors.ENDC)
        exit(0)
    
    print ('Tests failed')
    print ('  %d of %d ' % (failed_results, total_tests) +
           ('test' if total_tests == 1 else 'tests') + ' failed')
    exit(1)

if __name__ == '__main__':
    main()
