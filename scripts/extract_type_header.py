#!/usr/bin/env python3
#
# Dump type header for private types in c modules.
#
# Author: Malte Mues <mail.mues@gmail.com>

import os
import re
import shutil
import subprocess
import sys
import textwrap
from tempfile import TemporaryDirectory

DEFINE_REGEX_HEADER = re.compile(r"\s*#\s*define\s*([\w]+)")



def collect_defines(c_file):
    """Collects all defines in a c module.

    This function should collect all defines inside a c module.
    Than the script will add these defines to the type header file.
    This allows to use the defines in the harness as well. Because preprocessing
    eliminates them before compiling the goto binary,
    it is not possible to extract them from the goto binary.

    We assume that a define is either a single define. For example
    #define my_macro 0
    
    or eventually guarded by an ifdef, ifndef or if. For example:
    #ifdef another_macro
        #define my_macro
    #endif

    Any opening if*  is expected to be close by an #endif.
    Further, it is expected that #if and #endif pairs are not nested.
    
    The third group of defines that this script tries to catch are multiline
    macros:

    #define aMacro( X )                                   \
        if( ( X )->A == 1 )                               \
        {                                                 \
            ( X )->B = 2;                                 \
        }                                                 
    
    The assumption is that '\' is the last character in the line.
    """

    collector_result = ""
    with open(c_file, "r") as in_file:
        continue_define = False
        in_potential_def_scope = ""
        potential_define = False
        potential_define_confirmed = False
        for line in in_file:
            matched = DEFINE_REGEX_HEADER.match(line)
            if line.strip().startswith("#if"):
                potential_define = True
                in_potential_def_scope += line
            elif line.strip().startswith("#endif") and potential_define:
                if potential_define_confirmed:
                    in_potential_def_scope += line
                    collector_result += in_potential_def_scope
                in_potential_def_scope = ""
                potential_define = False
                potential_define_confirmed = False
            elif matched and potential_define:
                potential_define_confirmed = True
                in_potential_def_scope += line
            elif matched or continue_define:
                continue_define = line.strip("\n").endswith("\\")
                collector_result += line
            elif potential_define:
                in_potential_def_scope += line
    return collector_result


def get_module_name(c_file):
    base = os.path.basename(c_file)
    return base.split(".")[0]


def make_header_file(goto_binary, c_file, header_out=None):
    with TemporaryDirectory() as tmpdir:
        module = get_module_name(c_file)

        header_file = module + "_datastructure.h"

        drop_header_cmd = ["goto-instrument",
                           "--dump-c-type-header",
                           module,
                           goto_binary,
                           header_file]
        subprocess.run(drop_header_cmd,
                       stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT,
                       check=False,
                       universal_newlines=True,
                       cwd=tmpdir,
                       shell=False)

        header_file = os.path.normpath(os.path.join(tmpdir, header_file))
        with open(header_file, "a") as out:
            print(collect_defines(c_file), file=out)

        if header_out:
            absolut_header_target = os.path.normpath(
                os.path.abspath(header_out))
            shutil.move(header_file, absolut_header_target)
        else:
            with open(header_file, "r") as header:
                print("".join(header.readlines()))


def print_usage_and_exit():
    print(textwrap.dedent("""\
        This script extracts a type header for local types in a c file.
        It expects a goto binary compiled from the c file
        along with the original c file.

        extract_type_header.py my_goto_binary the_c_file [header_output]

        The header_output is an optional parameter specifying a target output
        file. Otherwise, the script is going to print the header to stdout.
        """))
    sys.exit(1)

if __name__ == '__main__':
    TARGET = None
    if len(sys.argv) < 3 or len(sys.argv) > 4:
        print_usage_and_exit()
    BINARY = sys.argv[1]
    if not os.path.isabs(BINARY):
        BINARY = os.path.normpath(os.path.join(os.getcwd(), BINARY))
    FILE = sys.argv[2]
    if not os.path.isabs(FILE):
        FILE = os.path.normpath(os.path.join(os.getcwd(), FILE))
    if len(sys.argv) == 4:
        TARGET = sys.argv[3]
        if not os.path.isabs(TARGET):
            TARGET= os.path.normpath(os.path.join(os.getcwd(), TARGET))
    make_header_file(BINARY, FILE, TARGET)
