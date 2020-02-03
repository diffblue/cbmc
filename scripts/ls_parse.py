#!/usr/bin/env python3
#
# Dump info about linker script symbols that pertain to addresses and sizes.
#
# Author: Kareem Khazem <karkhaz@amazon.com>
# Copyright Amazon, Inc. 2017


import ast
import argparse
import json
import logging
from   logging import error, warning, info, debug
import operator
import os
import re
import subprocess
import sys
import textwrap
import traceback

# ast.Num was deprecated in python 3.8
if sys.version_info.major > 3 or \
        (sys.version_info.major == 3 and sys.version_info.minor > 7):
    ast_num = ast.Constant
else:
    ast_num = ast.Num

def epilog():
    return textwrap.dedent("""
    This script generates a C file containing two kinds of information:

    - The values of symbols that are defined in a linker script; these
      are printed as C definitions, like
        char *bss_start = (char *)4070047185u;

    - The extent of ELF sections that are defined in a linker script;
      these are printed as CPROVER annotations, like
        __CPROVER_allocated_memory(0xe9fda44b, 4096);

    A goto-binary of this C file can be linked into the rest of the
    codebase that you wish to analyse. This provides CPROVER with
    definitions that it otherwise would not have access to, since they
    are defined in a linker script rather than C code. This information
    can also be printed in JSON rather than as a C file, so that CPROVER
    can invoke and use this script without user intervention.

    This script needs a list of symbols declared but never defined in C
    code. The hacky way of supplying this list is by passing the path to
    the codebase with the --dir flag; this script will scan the codebase
    for extern-declared variables. A better way is to generate that list
    with CPROVER, and pass that list in using --sym-file. The argument
    to --sym-file can be a filename, or '-' for stdin.
    """)


"""`Running-regex' linker script parser. We don't currently use a full
grammar, as we only need a fraction of the information contained in
linker scripts to give to CBMC. If in the future we need a more
sophisticated parser, we should use an actual grammar from a real
parser. GNU LD uses a YACC/Flex setup and has a very complete grammar,
but we cannot use it (GPL 3). LLD (the LLVM project's linker script
parser) is hand-written (so no explicit grammar), but they do not aim to
support all of GNU LD's syntax, so LLD doesn't work on some real linker
scripts. So in summary: use this regex parser while it's practical;
switch to LLD when needed, and possibly contribute to LLD development to
support parsing your use case."""
def get_linker_script_data(script):
    try:
        with open(script) as f:
            lines = f.read().splitlines()
    except IOError:
        error("Linker script '%s' not found", script)
        exit(1)

    text = " ".join(lines)
    text = re.sub(r"\s+", " ", text)

    # In these regexes, we always start by matching a whitespace. This
    # is so that we don't match every substring of an identifier. i.e.
    # if we have a section definition .text : { ..., then we only want
    # to recognise a section called ".text", and not also "text", "ext",
    # "xt", and "t".
    #
    # Just to be safe, ensure that the first character of the linker
    # script is a whitespace.
    text = " %s" % text

    # Lex out comments
    text = re.sub(r"/\*.*?\*/", " ", text)

    close_brace     = re.compile(r"\s}(\s*>\s*\w+)?")
    uwnknown_cmd    = re.compile(r"\sPHDRS\s*{")  # only this pattern for now, more might follow!
    memory_cmd      = re.compile(r"\sMEMORY\s*{")
    sections_cmd    = re.compile(r"\sSECTIONS\s*{")
    assign_current  = re.compile(r"\s(?P<sym>\w+)\s*=\s*\.\s*;")
    sec_def         = re.compile(r"\s(?P<sec>([-\.\w]+)|(/DISCARD/))"
                                 r"\s+([^:{};]*?):([^:{};])*?{")
    assign_size     = re.compile(r"\s(?P<sym>\w+)\s*=\s*SIZEOF\("
                                     r"(?P<sec>\.\w+)\)\s*;")
    memory_block    = re.compile(r"\s(?P<name>\w+)\s*:\s*ORIGIN\s*=\s*"
                                     r"(?P<orig>0x[a-fA-F0-9]+)\s*,\s*"
                                     r"LENGTH\s*=\s*(?P<len>\d+)\s*"
                                     r"(?P<unit>[KMG])")
    exp = r"(ORIGIN\(\w+\)|LENGTH\(\w+\))"
    op  = r"(\+|\-)"
    assign_expr     = re.compile(r"\s(?P<sym>\w+)\s*=\s*"
                                  r"(?P<expr>{exp}(\s*{op}\s*{exp})*)"
                                  r"\s*;".format(exp=exp, op=op))

    # If we match a regex, call the right function to update the state
    # with the info gleaned from the matched string.
    jump_table = {
        close_brace     : close_brace_fun,
        uwnknown_cmd    : unknown_cmd_fun,
        memory_cmd      : memory_cmd_fun,
        sections_cmd    : sections_cmd_fun,
        assign_current  : assign_current_fun,
        memory_block    : memory_block_fun,
        sec_def         : sec_def_fun,
        assign_size     : assign_size_fun,
        assign_expr     : assign_expr_fun,
    }

    # Whenever we match an interesting regex, we'll update the state
    # with whatever information we want to rip from that bit of text.
    state = {}

    # The section definition that we were last in.
    state["cur-sec"] = None

    # If we know what section *start* the current address (.) points to,
    # then this will not be None. It's used to match an assignment to
    # the start of a section.
    state["start-valid"] = None

    # If we have just seen an assignment, then this will not be None.
    # It's used to match up an assignment with the end of a section.
    state["end-valid"] = None

    # Each entry here maps a section name to a map. That map maps "size"
    # to the symbol pointing to the size of the section, and "start"
    # to the symbol pointing to the start address of the section. One of
    # "start" or "size" may be absent, if we couldn't get that bit of
    # information from the linker script.
    state["sections"] = {}

    # We can use the list of valid addresses to sanity-check that the
    # start addresses of sections are genuinely addresses.
    state["valid-addresses"] = []

    # Symbols that get some expression assigned to them, either inside
    # or outside a section definition. We'll match them up later.
    state["expr-assigns"] = []

    # These are to sanity-check the parsing.
    state["MEM"] = False
    state["SEC"] = False
    state["DEF"] = False
    state["UNKNOWN"] = False

    i = 0
    while i < len(text):
        buf = text[i:]
        i += 1
        asrt(not (state["MEM"] and state["SEC"]),
             "memory & sections", buf)
        asrt(not state["DEF"] or state["SEC"],
             "def outside SECTION", buf)

        jump_fun = None
        matched_str = None
        matched_re = None
        match = None
        for regex, fun in jump_table.items():
            m = regex.match(buf)
            if m:
                if jump_fun is not None:
                    error("matched multiple regexes\n%s", buf)
                    exit(1)
                jump_fun = fun
                match = m
                matched_str = buf[m.span()[0]:m.span()[1]]
                for s, v in locals().items():
                    if v is regex and s != "regex":
                        matched_re = s
        if jump_fun is not None:
            info("regex '%s' matched '%s'", matched_re, matched_str)
            jump_fun(state, match, buf)
            i = i + match.span()[1] - 1
        else:
            debug("Clobbering due to '%s'...", buf[:20])
            # There may have been some intermediate command between the
            # start of a section definition and where we are. So we have
            # no idea what address the current address pointer refers to
            state["start-valid"] = None
            # There may have been an intermediate command between the
            # last assignment and the end of the section.
            state["end-valid"] = None
    match_up_expr_assigns(state)
    return state


def assign_expr_fun(state, match, _):
    # Do NOT invalidate 'start-valid' here. Assignments from expressions
    # do not actually advance the current address pointer.
    sym, expr = match.group("sym"), match.group("expr")
    origin_pat = r"ORIGIN\((?P<block>\w+?)\)"
    origins = re.findall(origin_pat, expr)
    if len(origins) != 1:
        info("assign with %d origins, skipping: %s", len(origins),
               match.string())
        return
    ret = {"origin": origins[0], "sym": sym}
    for block_name, data in state["blocks"].items():
        for op in ["ORIGIN", "LENGTH"]:
            old_expr = str(expr)
            expr = re.sub(r"%s\(%s\)" % (op, block_name), str(data[op]),
                          expr)
            if expr != old_expr:
                info("Subbed %s(%s) with %d", op, block_name, data[op])
    try:
        ret["addr"] = safe_eval(expr)
    except RuntimeError:
        error("Unable to evaluate '%s'", expr)
        sys.exit(1)
    info("Evaluated '%s' to %d", expr, ret["addr"])
    state["expr-assigns"].append(ret)


def sec_def_fun(state, match, buf):
    asrt(not state["DEF"], "nested sec def", buf)
    state["DEF"] = True
    sec = match.group("sec")
    info("Current section is now '%s'", sec)
    state["cur-sec"] = sec
    state["start-valid"] = True


def assign_size_fun(state, match, buf):
    asrt(state["SEC"], "assignment outside SECTIONS", buf)
    sec = match.group("sec")
    if sec not in state["sections"]:
        state["sections"][sec] = {}
    sym = match.group("sym")
    info("'%s' marks the size of section '%s'", sym, sec)
    state["sections"][sec]["size"] = sym


def assign_current_fun(state, match, buf):
    asrt(state["SEC"], "assignment outside SECTIONS", buf)
    sec = state["cur-sec"]
    state["end-valid"] = match
    if state["start-valid"]:
        if sec not in state["sections"]:
            state["sections"][sec] = {}
        sym = match.group("sym")
        info("'%s' marks the start of section '%s'", sym, sec)
        state["sections"][sec]["start"] = sym
    else:
        info("Don't know where we are.")


def close_brace_fun(state, _, buf):
    # We might have seen an assignment immediately before this.
    if state["end-valid"]:
        asrt(state["DEF"], "end-valid outside sec-def", buf)
        sec = state["cur-sec"]
        if sec in state["sections"]:
            sym = state["end-valid"].group("sym")
            info("'%s' marks the end of section '%s'", sym, sec)
            state["sections"][sec]["end"] = sym
            state["end-valid"] = None
        else:
        # Linker script assigned end-of-section to a symbol, but not
        # the start. this is useless to us.
            pass

    if state["DEF"]:
        info("Closing sec-def")
        state["DEF"] = False
    elif state["SEC"]:
        info("Closing sections")
        state["SEC"] = False
    elif state["MEM"]:
        info("Closing memory command")
        state["MEM"] = False
    elif state["UNKNOWN"]:
        info("Closing unknown command")
        state["UNKNOWN"] = False
    else:
        error("Not in block\n%s", buf)
        traceback.print_stack()
        exit(1)


def memory_block_fun(state, m, buf):
    asrt(state["MEM"], "memory block outside MEMORY", buf)
    start, length, unit = m.group("orig"), m.group("len"), m.group("unit")
    length = int(length)
    dec_start = int(start, 16)
    mul = {"K": 1000, "M": 1000000, "G": 1000000000}
    length = length * mul[unit]
    end = dec_start + length
    info("mem block %s from %d to %d (%d%s long)", start, dec_start, end,
            length, unit)
    state["valid-addresses"].append({"from": dec_start, "to": end})

    name = m.group("name")
    if "blocks" not in state:
        state["blocks"] = {}
    state["blocks"][name] = {"ORIGIN": int(start, 16), "LENGTH": length}


def sections_cmd_fun(state, _, buf):
    asrt(not state["SEC"], "encountered SECTIONS twice", buf)
    state["SEC"] = True


def memory_cmd_fun(state, _, buf):
    asrt(not state["MEM"], "encountered MEMORY twice", buf)
    state["MEM"] = True


def unknown_cmd_fun(state, _, buf):
    asrt(not state["MEM"], "encountered UNKNOWN twice", buf)
    state["UNKNOWN"] = True


def match_up_expr_assigns(state):
    blocks = set([data["origin"] for data in state["expr-assigns"]])
    for block in blocks:
        assigns = [a for a in state["expr-assigns"]
                   if a["origin"] == block]
        assigns = sorted(assigns, key=(lambda a: a["addr"]))
        if len(assigns) < 2:
            warning("Only 1 assignment to expr involving %s", block)
            continue
        start_addr, end_addr = assigns[0]["addr"], assigns[-1]["addr"]
        start_sym, end_sym = assigns[0]["sym"], assigns[-1]["sym"]
        info("Valid memory from %s (%d) to %s (%s) [%s block]",
                start_sym, start_addr, end_sym, end_addr, block)
        tmp = {"start": start_sym, "end": end_sym}
        sec_name = "BLOCK_%s_%s-%s" % (block, start_sym, end_sym)
        state["sections"][sec_name] = tmp


def asrt(cond, msg, buf):
    if not cond:
        error("%s\n%s", msg, buf)
        exit(1)


def needed_definitions(all_symbols, root_dir):
    ret = []
    pat = re.compile(r"extern\s+char\s+(?P<var>\w+)\[\];")
    allowed = [".c", ".cpp", ".h"]
    for root, _, files in os.walk(root_dir):
        for file in files:
            file = os.path.join(root, file)
            _, ext = os.path.splitext(file)
            if ext not in allowed:
                continue
            with open(file) as f:
                for line in f:
                    m = pat.match(line)
                    if m:
                        ret.append(m.group("var"))
    bad = [v for v in ret if v not in all_symbols]
    if bad:
        logging.error("These symbols need definitions but are not "
                      "in the object file: %s", ", ".join(bad))
        exit(1)
    logging.info("need symbols:\n%s", "\n".join(ret))
    return ret


def symbols_from(object_file):
    cmd = ["objdump", "--syms", object_file]
    proc = subprocess.Popen(cmd, universal_newlines=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if proc.wait():
        logging.error("`%s` failed. Output:\n%s", " ".join(cmd),
                      proc.stdout.read())
        exit(1)
    pat = re.compile(r"(?P<addr>[^\s]+)\s+"
                     r"(?P<flags>[lgu! ][w ][C ][W ][Ii ][Dd ][FfO ])\s+"
                     r"(?P<section>[^\s]+)\s+"
                     r"(?P<size>[0-9a-f]+)\s+"
                     r"(?P<name>[^\s]*)" # Can be empty!
                    )
    matching = False
    ret = {}
    for line in proc.stdout.read().splitlines():
        if not line:
            continue
        if not matching and re.match("SYMBOL TABLE:", line):
            matching = True
            continue
        if not matching:
            continue
        m = pat.match(line)
        if not m:
            logging.error("Unexpected line from `%s`:\n%s",
                    " ".join(cmd), line)
            exit(1)
        ret[m.group("name")] = m.group("addr")
    logging.info("found symbols:\n%s", "\n".join(
        ["0x%-16s %s" % (v, k) for k, v in ret.items()]))
    return ret


def match_up_addresses(script_data, symbol_table):
    ret = []
    for name, data in script_data["sections"].items():
        ok = False
        if "size" in data and "start" in data:
            ok = True
        if "end" in data and "start" in data:
            ok = True
        if not ok:
            continue
        region = {}
        for sym, value in symbol_table.items():
            if "size" in data and sym == data["size"]:
                region["size"] = {"sym": sym, "val": value}
            if "start" in data and sym == data["start"]:
                region["start"] = {"sym": sym, "val": value}
            if "end" in data and sym == data["end"]:
                region["end"] = {"sym": sym, "val": value}
            region["section"] = name
        append = False
        if "size" in region and "start" in region:
            append = True
        if "end" in region and "start" in region:
            append = True
        if append:
            ret.append(region)
    return ret


def get_region_range(region):
    ret = {}
    if "end" in region:
        start = int(region["start"]["val"], 16)
        end = int(region["end"]["val"], 16)
        size = end - start
        s_var = region["start"]["sym"]
        e_var = region["end"]["sym"]
        ret["start"] = start
        ret["size"] = size
        ret["start-symbol"] = s_var
        ret["end-symbol"] = e_var
        ret["has-end-symbol"] = True
        ret["annot"] = "__CPROVER_allocated_memory(%s, %d);" % (hex(start), size)
        ret["commt"] = "from %s to %s" % (s_var, e_var)
    elif "size" in region:
        start = int(region["start"]["val"], 16)
        size = int(region["size"]["val"], 16)
        s_var = region["start"]["sym"]
        z_var = region["size"]["sym"]
        ret["start"] = start
        ret["size"] = size
        ret["start-symbol"] = s_var
        ret["size-symbol"] = z_var
        ret["has-end-symbol"] = False
        ret["annot"] = "__CPROVER_allocated_memory(%s, %d);" % (hex(start), size)
        ret["commt"] = "from %s for %s bytes" % (s_var, z_var)
    else:
        raise "Malformatted region\n%s" % str(region)
    ret["section"] = region["section"]
    return ret


def final_json_output(regions, symbol_table):
    ret = {"regions": [], "addresses": []}
    for s, v in symbol_table.items():
        ret["addresses"].append({"sym": s, "val": int(v, 16)})
    for region in regions:
        ret["regions"].append(get_region_range(region))
    return ret


def symbols_from_file(sym_file):
    if sym_file == "-":
        return [s.strip() for s in sys.stdin.readlines()]
    with open(sym_file) as f:
        return [s.strip() for s in f.readlines()]


def safe_eval(expr):
    tree = ast.parse(expr, mode="eval").body

    def eval_single_node(node):
        logging.debug(node)
        if isinstance(node, ast_num):
            return node.n
        if isinstance(node, ast.BinOp):
            left = eval_single_node(node.left)
            right = eval_single_node(node.right)
            op = eval_single_node(node.op)
            return op(left, right)
        return {
            ast.Add: operator.add,
            ast.Sub: operator.sub,
            ast.Mult: operator.mul,
            # Use floordiv (i.e. //) so that we never need to
            # cast to an int
            ast.Div: operator.floordiv,
        }[type(node)]

    return eval_single_node(tree)


def main():
    pars = argparse.ArgumentParser(
        description="Generate info about linker-defined symbols and regions.",
        epilog=epilog(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    pars.add_argument("-s", "--script", metavar="S", required=True,
                      help="path to linker script")
    pars.add_argument("-o", "--object", metavar="O", required=True,
                      help="path to fully-linked binary")

    sym_source = pars.add_mutually_exclusive_group(required=True)
    sym_source.add_argument("-d", "--dir", metavar="D",
                      help="path to top-level of codebase")
    sym_source.add_argument("-i", "--sym-file",
            metavar="F", help="file of names of linker symbols")

    pars.add_argument("-t", "--out-file", metavar="F",
                      help="default: stdout", default=None)

    verbs = pars.add_mutually_exclusive_group()
    verbs.add_argument("-v", "--verbose", action="store_true")
    verbs.add_argument("-w", "--very-verbose", action="store_true")

    args = pars.parse_args()

    if args.verbose:
        lvl = logging.INFO
    elif args.very_verbose:
        lvl = logging.DEBUG
    else:
        lvl = logging.WARNING
    form = "linkerscript parse %(levelname)s: %(message)s"
    logging.basicConfig(format=form, level=lvl)

    script_data = get_linker_script_data(args.script)
    symbol_table = symbols_from(args.object)
    if args.dir:
        needed = needed_definitions(symbol_table.keys(), args.dir)
    else:
        needed = symbols_from_file(args.sym_file)
    symbol_table = {k:v for k, v in symbol_table.items() if k in needed}

    regions = match_up_addresses(script_data, symbol_table)

    info("symbol table %s" % json.dumps(symbol_table, indent=2))
    info("script data %s" % json.dumps(script_data, indent=2))
    info("regions %s" % json.dumps(regions, indent=2))

    final = json.dumps(final_json_output(regions, symbol_table),
                       indent=2)
    if args.out_file:
        with open(args.out_file, "w") as f:
            f.write(final)
        info(final)
    else:
        print(final)


if __name__ == "__main__":
    main()
