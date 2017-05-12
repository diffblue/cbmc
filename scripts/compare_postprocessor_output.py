import difflib, argparse, subprocess, sys, os, multiprocessing, itertools


def preprocess(compiler, file_contents):
    """ Get output from the preprocessing pass on a file.  """
    return subprocess.Popen(
            [compiler, '-E', '-'],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            stdin=subprocess.PIPE).communicate(input=file_contents)[0]


def preprocess_file(compiler, filename):
    """ Open a file and get the preprocessor output.  """
    with open(filename, 'rb') as f:
        return preprocess(compiler, f.read())


def remove_empty_lines(text):
    """ Remove empty lines from text.  """
    return '\n'.join(filter(None, text.splitlines()))


def file_contents_from_branch(filename, branch):
    """ Get a copy of a file from another branch and return its contents.  """
    return subprocess.check_output(
            ['git', 'show', '%s:%s' % (branch, filename)])


def equal_to_file_on_branch(filename, branch, compiler):
    """
    Open a file on this branch and preprocess it.  Preprocess the same file
    from another branch, and return whether the two files have (for all intents
    and purposes) the same contents.
    """
    with open(filename, 'rb') as f:
        def p(text):
            return preprocess(compiler, text)
        return (p(f.read()) ==
                p(file_contents_from_branch(filename, branch)))


def process_single_file(filename, branch, compiler):
    """ Like equal_to_file_on_branch, but also checks the file extension.  """
    _, ext = os.path.splitext(filename)
    return ((ext == '.h' or ext == '.cpp') and
            not equal_to_file_on_branch(filename, branch, compiler))


def is_source(filename):
    """ Return whether the file appears to be a C++ source file.  """
    _, ext = os.path.splitext(filename)
    return ext == '.h' or ext == '.cpp'


def process(tup):
    """
    Check a single file, and return its name if the check fails, otherwise
    return None.
    """
    failed = process_single_file(*tup)
    return file if failed else None


def main():
    """
    Open a file and compare its preprocessor output to the output from the same
    file on a different branch.  Return 0 if the outputs match, or 1 otherwise.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument(
            '--branch', type=str, default='upstream/master',
            help='The branch to compare')
    parser.add_argument(
            '--compiler', type=str, default='gcc',
            help='The compiler to use')
    args = parser.parse_args()

    all_files = [os.path.join(root, file)
            for root, _, files in os.walk('.') for file in files]
    source_files = filter(is_source, all_files)

    zipped = zip(
            source_files,
            itertools.cycle([args.branch]),
            itertools.cycle([args.compiler]))

    results = filter(None, multiprocessing.Pool(10).map(process, zipped))

    if results:
        print('\n'.join(results))
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
