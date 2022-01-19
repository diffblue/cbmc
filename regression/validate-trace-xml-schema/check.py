import os
import subprocess
import sys
import tempfile
import glob

this_script_dir = os.path.abspath(os.path.dirname(__file__))

TraceXsd = os.path.abspath(os.path.join(this_script_dir, '..', '..', 'doc/assets/xml_spec.xsd'))

test_base_dir = os.path.abspath(os.path.join(this_script_dir, '..', 'cbmc'))

# some tests in the cbmc suite don't work for the trace checks for one reason or another
ExcludedTests = list(map(lambda s: os.path.join(test_base_dir, s[0], s[1]), [
    # these tests dump the raw SMT2 output (using --outfile)
    ['array_of_bool_as_bitvec', 'test-smt2-outfile.desc'],
    # these tests expect input from stdin
    ['json-interface1', 'test_wrong_option.desc'],
    ['json-interface1', 'test.desc'],
    ['json-interface1', 'test_wrong_flag.desc'],
    ['xml-interface1', 'test_wrong_option.desc'],
    ['xml-interface1', 'test.desc'],
    ['xml-interface1', 'test_wrong_flag.desc'],
    # these want --show-goto-functions instead of producing a trace
    ['integer-assignments1', 'integer-typecheck.desc'],
    ['destructors', 'compound_literal.desc'],
    ['destructors', 'enter_lexical_block.desc'],
    ['enum_is_in_range', 'format.desc'],
    ['r_w_ok9', 'simplify.desc'],
    ['reachability-slice-interproc2', 'test.desc'],
    # this one wants show-properties instead producing a trace
    ['show_properties1', 'test.desc'],
    # program-only instead of trace
    ['vla1', 'program-only.desc'],
    ['Pointer_Arithmetic19', 'test.desc'],
    ['Quantifiers-simplify', 'simplify_not_forall.desc'],
    ['array-cell-sensitivity15', 'test.desc'],
    # these test for invalid command line handling
    ['bad_option', 'test_multiple.desc'],
    ['bad_option', 'test.desc'],
    ['unknown-argument-suggestion', 'test.desc'],
    # this one produces XML intermingled with main XML output when used with --xml-ui
    ['graphml_witness2', 'test.desc'],
    # these are producing coverage goals which aren't included in the schema
    ['cover-failed-assertions', 'test.desc'],
    ['cover-failed-assertions', 'test-no-failed-assertions.desc'],
    # produces intermingled XML on the command line
    ['coverage_report1', 'test.desc'],
    ['coverage_report1', 'paths.desc'],
    ['graphml_witness1', 'test.desc'],
    ['switch8', 'program-only.desc'],
    ['Failing_Assert1', 'dimacs.desc'],
    # this uses json-ui (fails for a different reason actually, but should also
    #   fail because of command line incompatibility)
    ['json1', 'test.desc'],
    # uses show-goto-functions
    ['reachability-slice', 'test.desc'],
    ['reachability-slice', 'test2.desc'],
    ['reachability-slice', 'test3.desc'],
    ['reachability-slice-interproc', 'test.desc'],
    ['unsigned1', 'test.desc'],
    ['reachability-slice-interproc3', 'test.desc'],
    ['sync_lock_release-1', 'symbol_per_type.desc'],
    # this test is marked smt-backend, and would thus fail as we run tests with
    # the SAT back-end only
    ['integer-assignments1', 'test.desc'],
    # this test is expected to abort, thus producing invalid XML
    ['String_Abstraction17', 'test.desc']
]))

# TODO maybe consider looking them up on PATH, but direct paths are
#      harder to get wrong
if len(sys.argv) != 3:
    sys.stderr.write('Usage: check.py <path-to-cbmc> <path-to-xmllint>')
CbmcPath = os.path.abspath(sys.argv[1])
XmlLintPath = os.path.abspath(sys.argv[2])


class ChangeDir:
    def __init__(self, change_to_wd):
        self.current_wd = os.getcwd()
        self.change_to_wd = change_to_wd

    def __enter__(self):
        os.chdir(self.change_to_wd)

    def __exit__(self, _type, _value, _tb):
        os.chdir(self.current_wd)


class TestSpec:
    def __init__(self, args, is_knownbug, is_future, is_thorough):
        self.args = args
        self.is_knownbug = is_knownbug
        self.is_future = is_future
        self.is_thorough = is_thorough


class Validator:
    def __init__(self, total_desc_count):
        self.failed_tests = []
        self.total_desc_count = total_desc_count
        self.checked_desc_count = 0

    def check_test_desc(self, test_desc_path):
        self.checked_desc_count += 1
        sys.stdout.write('*** Checking [{}/{}] {}... '.format(
            self.checked_desc_count, self.total_desc_count, test_desc_path))
        sys.stdout.flush()
        spec = self.read_spec(test_desc_path)
        if spec.is_knownbug:
            print('[Skipping KNOWNBUG]')
            return
        elif spec.is_future:
            print('[Skipping FUTURE]')
            return
        elif spec.is_thorough:
            print('[Skipping THOROUGH]')
            return
        test_desc_dir = os.path.dirname(test_desc_path)
        with ChangeDir(test_desc_dir):
            with tempfile.TemporaryFile() as trace_file:
                self.read_trace_into(trace_file, spec.args)
                trace_file.seek(0)
                self.check_trace(test_desc_path, trace_file)

    def read_trace_into(self, trace_file, args):
        subprocess.run([CbmcPath, '--trace', '--xml-ui'] + args,
                       stdout=trace_file)

    def check_trace(self, test_desc_path, trace_file):
        validate_result = subprocess.run([XmlLintPath,
                                          '--noout',  # we don't want it to print the XML we pipe in
                                          '--schema', TraceXsd,
                                          '-'  # read from STDIN
                                          ],
                                         stdin=trace_file,
                                         stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE)
        if validate_result.returncode == 0:
            sys.stdout.buffer.write(b'[SUCCESS]\n')
        else:
            sys.stdout.buffer.write(b'[FAILURE]\n')
            self.failed_tests.append(test_desc_path)
            sys.stdout.buffer.write(validate_result.stdout)
            sys.stdout.buffer.write(validate_result.stderr)

    def read_spec(self, test_desc_path):
        with open(test_desc_path) as test_desc_file:
            test_tags = test_desc_file.readline().split()
            source_file = test_desc_file.readline().strip()
            extra_args = test_desc_file.readline().split()
        is_future = 'FUTURE' in test_tags
        is_thorough = 'THOROUGH' in test_tags
        is_knownbug = 'KNOWNBUG' in test_tags
        return TestSpec(args=[source_file] + extra_args,
                        is_thorough=is_thorough,
                        is_future=is_future,
                        is_knownbug=is_knownbug)

    def has_failed_tests(self):
        return len(self.failed_tests) > 0

    def report(self):
        print('{}/{} tests succeed'.format(self.checked_desc_count - len(self.failed_tests), self.checked_desc_count))
        if self.has_failed_tests():
            print('Failed tests:')
            for spec in self.failed_tests:
                print(spec)


test_desc_files = list(
    filter(lambda s: s not in ExcludedTests, glob.glob(os.path.join(test_base_dir, '*/*.desc'))))
validator = Validator(total_desc_count=len(test_desc_files))
for test_desc in test_desc_files:
    validator.check_test_desc(test_desc)
validator.report()
if validator.has_failed_tests():
    sys.exit(1)
