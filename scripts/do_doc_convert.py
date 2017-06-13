from reformat_docs import convert_file
from os import walk
from os.path import join
from sys import exit
from re import match

"""
Run this from CBMC's top-level directory.
"""

def main():
    IGNORE_LIST = [
            r'src/big-int/.*',
            r'src/miniz/.*',
            r'src/ansi-c/arm_builtin_headers.h',
            r'src/ansi-c/clang_builtin_headers.h',
            r'src/ansi-c/cw_builtin_headers.h',
            r'src/ansi-c/gcc_builtin_headers_alpha.h',
            r'src/ansi-c/gcc_builtin_headers_arm.h',
            r'src/ansi-c/gcc_builtin_headers_generic.h',
            r'src/ansi-c/gcc_builtin_headers_ia32-2.h',
            r'src/ansi-c/gcc_builtin_headers_ia32.h',
            r'src/ansi-c/gcc_builtin_headers_mips.h',
            r'src/ansi-c/gcc_builtin_headers_power.h',
            r'src/ansi-c/library/cprover.h']

    MATCH_EXPR = r'.*\.(h|cpp)'

    for root, dirs, files in walk('src'):
        for file in files:
            path = join(root, file)
            if any(map(lambda x: match(x, path), IGNORE_LIST)):
                print 'ignoring', path
                continue
            if not match(MATCH_EXPR, path):
                continue
            convert_file(path, True)

if __name__ == '__main__':
    exit(main())
