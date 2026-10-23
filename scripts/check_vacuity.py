#!/usr/bin/env python3
"""Check that regression tests expecting VERIFICATION SUCCESSFUL are not
vacuous, i.e., that the end of their main function is reachable.

A test whose every path is cut by an unwinding or depth bound, or ends in an
assumption that does not hold, passes whatever its assertions say.  For each
selected test, a copy of its source gets

  __CPROVER_assert(0, "__vacuity_reach");

before the last top-level `return' of each definition of main (or before its
closing brace), and cbmc runs with the test's options.  The test is

  REACHED      if that assertion fails, i.e., some path reaches it;
  UNREACHED    if it holds: the test is vacuous;
  ERROR        if cbmc gives no result for it (conversion error, timeout).

Selected are the tests of the given directories whose level is CORE, whose
expected output (before the first `--') contains ^VERIFICATION SUCCESSFUL$,
or ^EXIT=0$ without an option that only displays the program (--show-*,
...), and which carry none of the excluded tags (as test.pl -X) nor the tag
`no-vacuity-check' (for a test whose main legitimately does not end, e.g.,
one that returns from every branch of a try block).  Tests with more than one
source file are skipped.

The exit status is 1 if any selected test is UNREACHED or ERROR.

usage: check_vacuity.py [-c CBMC] [-j JOBS] [-t TIMEOUT] [-X TAG]...
                        DIRECTORY...
The memory limit of each cbmc run is CBMC_TEST_MEMLIMIT (KiB), as for
test.pl.
"""

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys

MARK = '__vacuity_reach'
SOURCE_SUFFIXES = ('.c', '.i', '.cpp', '.cc', '.ii')
# options with which cbmc does not verify the program
DISPLAY_OPTIONS = (
    '--version', '--help', '--list-goto-functions', '--dump-c', '--dump-cpp',
    '--preprocess', '--test-preprocessor', '--validate-goto-binary',
    '--symex-coverage-report')


def find_main_body(src, match):
    """The positions of the opening and closing brace of the body that starts
    at the end of `match', and of its last top-level `return' (or None)."""
    start = match.end() - 1
    depth = 0
    i = start
    n = len(src)
    last_return = None
    while i < n:
        c = src[i]
        if src.startswith('//', i):
            i = src.find('\n', i)
            if i < 0:
                return None
            continue
        if src.startswith('/*', i):
            i = src.find('*/', i)
            if i < 0:
                return None
            i += 2
            continue
        if c in '"\'':
            i += 1
            while i < n and src[i] != c:
                i += 2 if src[i] == '\\' else 1
            i += 1
            continue
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                return start, i, last_return
        elif (depth == 1 and src.startswith('return', i) and
              not (src[i - 1].isalnum() or src[i - 1] == '_') and
              i + 6 < n and not (src[i + 6].isalnum() or src[i + 6] == '_')):
            last_return = i
        i += 1
    return None


def instrument(src):
    """`src' with the reachability assertion at the end of each definition
    of main (alternatives under #if each get one), or None."""
    points = []
    for match in re.finditer(r'\bint\s+main\s*\([^)]*\)\s*\{', src):
        body = find_main_body(src, match)
        if body is not None:
            _, close, last_return = body
            points.append(last_return if last_return is not None else close)
    if not points:
        return None
    for at in sorted(points, reverse=True):
        src = src[:at] + '__CPROVER_assert(0, "%s");\n' % MARK + src[at:]
    return src


def selected(desc_lines, excluded_tags):
    """Whether a test with these test.desc lines is to be checked."""
    if len(desc_lines) < 3:
        return False
    tags = desc_lines[0].split()
    if not tags or tags[0] != 'CORE':
        return False
    if 'no-vacuity-check' in tags or any(t in excluded_tags for t in tags):
        return False
    expected = []
    for line in desc_lines[3:]:
        if line.strip() == '--':
            break
        expected.append(line.strip())
    # success is required: the verdict, or the exit status 0 of a run that
    # verifies (not one that only displays the program)
    if '^VERIFICATION SUCCESSFUL$' in expected:
        return True
    display_only = any(o.startswith('--show-') or o in DISPLAY_OPTIONS
                       for o in desc_lines[2].split())
    return '^EXIT=0$' in expected and not display_only


def check(cbmc, timeout, desc_path):
    """The result for the test of `desc_path'."""
    directory = os.path.dirname(desc_path)
    lines = open(desc_path, errors='replace').read().split('\n')
    source, options = lines[1].strip(), lines[2].strip()
    other_sources = [
        o for o in options.split() if o.endswith(SOURCE_SUFFIXES)]
    if (' ' in source or not source.endswith(SOURCE_SUFFIXES) or
            other_sources):
        return desc_path, 'SKIPPED', 'more than one source file'
    try:
        src = open(os.path.join(directory, source), errors='replace').read()
    except OSError:
        return desc_path, 'SKIPPED', 'no source file'
    instrumented = instrument(src)
    if instrumented is None:
        return desc_path, 'SKIPPED', 'no definition of main'
    base, ext = os.path.splitext(source)
    copy = os.path.join(
        directory,
        '%s__vacuity_%s%s' % (base, os.path.basename(desc_path)[:-5], ext))
    with open(copy, 'w') as f:
        f.write(instrumented)
    limit = os.environ.get('CBMC_TEST_MEMLIMIT')
    command = '%s %s %s' % (cbmc, options, os.path.basename(copy))
    if limit:
        command = 'ulimit -v %s; %s' % (limit, command)
    try:
        process = subprocess.run(
            ['bash', '-c', command], cwd=directory, capture_output=True,
            text=True, errors='replace', timeout=timeout)
        output = process.stdout + process.stderr
    except subprocess.TimeoutExpired:
        return desc_path, 'ERROR', 'timeout after %d s' % timeout
    finally:
        os.remove(copy)
    result = re.search(r'%s: (SUCCESS|FAILURE)' % MARK, output)
    if result is None:
        last = output.strip().split('\n')[-1] if output.strip() else ''
        return desc_path, 'ERROR', 'no result (%s)' % last
    if result.group(1) == 'SUCCESS':
        return desc_path, 'UNREACHED', 'the end of main is unreachable'
    return desc_path, 'REACHED', ''


def main():
    parser = argparse.ArgumentParser(
        description=__doc__.split('\n\n')[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-c', '--cbmc', default='cbmc',
                        help='the cbmc command (default: cbmc)')
    parser.add_argument('-j', '--jobs', type=int, default=1)
    parser.add_argument('-t', '--timeout', type=int, default=900,
                        help='seconds per test (default: 900)')
    parser.add_argument('-X', '--exclude', action='append', default=[],
                        metavar='TAG', help='exclude tests with this tag')
    parser.add_argument('directories', nargs='+')
    args = parser.parse_args()
    # cbmc runs in each test's directory
    executable, _, rest = args.cbmc.partition(' ')
    if os.sep in executable:
        args.cbmc = (os.path.abspath(executable) + ' ' + rest).rstrip()

    tests = []
    for directory in args.directories:
        for test in sorted(os.listdir(directory)):
            test_dir = os.path.join(directory, test)
            if not os.path.isdir(test_dir):
                continue
            for name in sorted(os.listdir(test_dir)):
                if not name.endswith('.desc'):
                    continue
                desc_path = os.path.join(test_dir, name)
                lines = open(desc_path, errors='replace').read().split('\n')
                if selected(lines, args.exclude):
                    tests.append(desc_path)

    counts = {}
    problems = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as executor:
        for desc_path, result, detail in executor.map(
                lambda d: check(args.cbmc, args.timeout, d), tests):
            counts[result] = counts.get(result, 0) + 1
            if result in ('UNREACHED', 'ERROR'):
                problems.append((desc_path, result, detail))
                print('%s: %s (%s)' % (result, desc_path, detail), flush=True)

    print('%d tests: %s' % (
        len(tests),
        ', '.join('%d %s' % (counts[r], r) for r in sorted(counts))))
    if problems:
        print('A test whose main never ends passes whatever it asserts: '
              'raise its bounds (--unwind, --depth), or tag it '
              'no-vacuity-check if main legitimately does not end.')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
