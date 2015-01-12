#!/usr/bin/env python3

# (1) Wrap if, while, etc. statements in curly braces.
# (2) Insert fences; backup file as *.fibak first if it does not exist yet

# Transformations preserve line numbers.

# ------------------------------------------------------------------------------
# Current musketeer input format (SVN rev >= 4816)

# Input format example (musketeer output; 9 cols):
# fence|peterson.c|thr1|6|c::turn|peterson.c|thr1|7|c::flag2

# Input format example (for e.g. pensieve output; 5 cols):
# fence|peterson.c|5|c::flag1|0

# ------------------------------------------------------------------------------
# Old musketeer input formats:

# Input format example (for regular musketeer output; fixed version; 9 cols):
# fence|test.c|test|5|c::exp|test.c|test|5|c::exp

# Input format example (for regular musketeer output; async version;
# unsupported; 11 cols):
# fence|test.c|test|5|exp|c::exp|test.c|test|5|exp|c::exp

# Input format example (for regular musketeer output; with types; unsupported;
# 13 cols):
# dp|pfscan.c|matchfun|311|line_f|c::line_f|signed_int|f.c|fun|31|*mutex|c::p_l|
# (notice that there's no type for the second access)

# Input format example (for e.g. allshared output; 5 cols):
# fence|assoc.c|125|old_hashtable|Write

# ------------------------------------------------------------------------------
# Implementation notes

# - The newline that terminates a line is considered part of the line.
# - Two ways of specifying lines: line number (1-based), or global index of
#   character (0-based).
# - Conceptually, the C file is analyzed by moving around a cursor that points
#   at characters in the input file. Various functions are provided to move the
#   cursor (e.g. ln_toe() moves the cursor to the end of the current line).
# - Common argument names: pos (cursor position), s (string containing source
#   file)
# - Assumption: Input is a well-formed C file.
# - Whitespace (e.g. for eat() and puke()): space, tab, newline.
# - Functions that take ranges of cursor positions treat both as inclusive.
# - Most important top-level functions: insert_fences(), place_fence(),
#   place_dp().
# - Two types of temporary variables: pull variable, connection variable. For
#   the pull variable we need the correct type of the expression.

# ------------------------------------------------------------------------------

# Todo:
# - Comment handling, e.g. comments at end of line (priority low)

# ------------------------------------------------------------------------------

import re
import sys
import shutil
import os

# ------------------------------------------------------------------------------
# Fence map (for ARM and dp only used when dependency insertion is not possible)

fm_x86 = { 'fence': 'mfence' }
fm_arm = { 'fence': 'dsb', 'cf': 'isb', 'dp': 'dsb' }

# ------------------------------------------------------------------------------
# Configuration parameters set via command line arguments.

handle_dp = False
musk_form = True
fm = fm_x86

# ------------------------------------------------------------------------------
# Indices of items in lines in results.txt in musk format
# -1: gets last element from list

im_fence = 0

im_src_file1 = 1
im_func_name1 = 2
im_line1 = 3
im_exp1 = -1
im_cprover_exp1 = -1
im_type1 = -1

im_src_file2 = 5
im_func_name2 = 6
im_line2 = 7
im_exp2 = -1
im_cprover_exp2 = -1
im_type2 = -1

# ------------------------------------------------------------------------------
# Indices of items in lines in results.txt in other format

io_fence = 0
io_src_file = 1
io_line = 2

# ------------------------------------------------------------------------------

# Enum for possible fence positions
fence_first, fence_second = range(2)

# Config for fence position (where to insert into the code)
fence_pos = fence_first

# ------------------------------------------------------------------------------

def print_err(s):
  print(s, file = sys.stderr)

def assert_msg(c, msg):
  if not c:
    print_err(msg)
    assert(False)

def usage():
  print_err("Usage:")
  print_err("  fi.py (x86|arm) (fence|dp) (musk|other) <results>")
  print_err("")
  print_err("  1: Architecture")
  print_err("  2: Select if fence or real dependency should be used for dp's")
  print_err("  3: Specify input format")
  print_err("  4: Output file of musketeer (results.txt)")

# ------------------------------------------------------------------------------
# Functions to delete, replace, and insert symbols from/in a string

### Insert string at position in string
# :pos is exclusive, pos: is inclusive
def insert(s, pos, c):
  return s[:pos] + c + s[pos:]

### Delete string between pos1 (inclusive) and pos2 (exclusive)
def delete(s, pos1, pos2):
  assert(pos1 <= pos2)
  return s[:pos1] + s[pos2:]

### Get line within string (including newline at end)
# pos: position within a line
def extract_ln(s, pos):
  start = ln_tos(s, pos)
  end = ln_toe(s, pos)
  ss = s[start:end+1]
  return ss

### Replace regex on line with repl (regex must match on line)
# Current limitation: only string replacement
def replace_ln(s, pos, regex, repl):
  start = ln_tos(s, pos)
  end = ln_toe(s, pos)
  ln = extract_ln(s, pos)
  #lnt = re.sub(regex, ln, repl)
  lnt = ln.replace(regex, repl, 1)
  assert(ln != lnt);
  s = delete(s, start, end + 1)
  s = insert(s, start, lnt)
  return s

### Insert curly braces at specified positions
def wrap(s, pos1, pos2):
  assert(pos1 < pos2)
  assert(pos2 < len(s))
  s = insert(s, '{', pos1)
  s = insert(s, '}', pos2 + 1)
  return s

### Insert items at given positions of string (l is a list of pairs)
# Items to insert must be single characters
def insert_items(s, l):
  l.sort()
  cnt = 0
  for el in l:
    s = insert(s, el[0] + cnt, el[1])
    cnt += 1
  return s

# ------------------------------------------------------------------------------
# Functions to move cursor to start or end of specific lines.

### Goto start of line of a certain number
# return value: index of first char on line, -1 if line does not exist
def before_line(s, n):
  assert(n >= 1)
  cnt = 1
  for i in range(0, len(s)):
    if cnt == n:
      return i
    if s[i] == '\n':
      cnt += 1
  return -1

### Goto end of line of a certain number
# return value: index of newline at end of line
def after_line(s, n):
  return before_line(s, n + 1) - 1

# ------------------------------------------------------------------------------
# Functions to move cursor to start or end of line, given a position.

### Go from end to start of line
def ln_etos(s, pos):
  assert(s[pos] == '\n')
  return ln_tos(s, pos)

### Go from start to end of line
def ln_stoe(s, pos):
  assert(s[pos] != '\n')
  return ln_toe(s, pos)

### Go to start of line
def ln_tos(s, pos):
  assert(pos > 0)
  if s[pos] == '\n':
    pos -= 1

  while pos > 0 and s[pos] != '\n':
    pos -= 1

  if s[pos] == '\n':
    pos += 1
    assert(s[pos] != '\n')
    return pos
  assert(False)

### Go to end of line
def ln_toe(s, pos):
  assert(pos > 0)
  l = len(s)
  while pos < l and s[pos] != '\n':
    pos += 1

  if s[pos] == '\n':
    return pos
  assert(False)

# ------------------------------------------------------------------------------
# Functions to skip over text items. It is an error to skip to the end of the
# string.

def next_item(s, pos, item):
  l = len(s)
  assert(pos < l)
  ret = s.find(item, pos)

  # Debug
  if (ret == -1):
    assert(s[pos] == '\n')
    print('Debug: string for next_item:')
    print(s[pos:])

  return ret

### Get next semicolon at or after pos
# return value: index of next semicolon, or -1
def next_semicolon(s, pos):
  return next_item(s, pos, ';')

### Skip over nested items (return pos of next character), forwards or backwards
# s: file as string
# a: left item
# b: right item
# d: direction(1: forward, -1: backward)
# pos: points at first item (a for forward, b for backward)
def skip_nested(s, a, b, d, pos):
  l = len(s)
  assert(pos < l)
  assert(pos >= 0)
  assert(d == -1 or d == 1);
  assert(d != 1 or s[pos] == a);
  assert(d != -1 or s[pos] == b);

  cnt = d
  pos += d
  while True:
    assert(pos >= 0)
    assert(pos < l)
    if s[pos] == a:
      cnt += 1
    elif s[pos] == b:
      cnt -= 1

    pos += d

    if cnt == 0:
      assert(pos >= 0)
      assert(pos < l)
      return pos

  assert(False)

def skip_p(s, pos):
  return skip_nested(s, '(', ')', 1, pos)

def skip_b(s, pos):
  return skip_nested(s, '{', '}', 1, pos)

def skip_p_b(s, pos):
  return skip_nested(s, '(', ')', -1, pos)

def skip_b_b(s, pos):
  return skip_nested(s, '{', '}', -1, pos)

# Return position of current or next non-whitespace character
def eat(s, pos):
  l = len(s)
  assert(pos < l)
  while (pos < l):
    c = s[pos]
    if c != ' ' and c != '\t' and c != '\n':
      return pos
    pos += 1
  assert(False)
  return pos

# Return position of current or previous non-whitespace character.
def puke(s, pos):
  l = len(s)
  assert(pos < l)
  while (pos < l):
    c = s[pos]
    if c != ' ' and c != '\t' and c != '\n':
      return pos
    pos -= 1
  assert(False)
  return pos

# Return position of current or previous non-whitespace character (newline is
# not considered a whitespace character here).
def puke2(s, pos):
  l = len(s)
  assert(pos < l)
  while (pos < l):
    c = s[pos]
    if c != ' ' and c != '\t':
      return pos
    pos -= 1
  assert(False)
  return pos

### Skip over statement (including parentheses).
def skip_stat(s, pos):
  l = len(s)
  assert(pos < l)
  # Skip keyword
  if (s[pos:pos+5] == 'while'):
    pos += 5
  elif (s[pos:pos+2] == 'if'):
    pos += 2
  elif (s[pos:pos+3] == 'for'):
    pos += 3
  elif (s[pos:pos+6] == 'switch'):
    pos += 6
  else:
    return -1
  pos = eat(s, pos)
  if (s[pos] != '('):
    # Spurious statement (e.g. in comment or string)
    return -1
  pos = skip_p(s, pos)
  pos = eat(s, pos)
  return pos

# ------------------------------------------------------------------------------
# Predicates

# Are the nested constructions with symbols a, b balanced between pos1 and pos2?
def is_balanced(s, a, b, pos1, pos2):
  assert(pos1 < pos2)
  assert(pos2 < len(s))
  cnt = 0
  for i in range(pos1, pos2+1):
    if s[i] == a:
      cnt += 1    
    elif s[i] == b:
      cnt -= 1
  if cnt == 0:
    return True
  return False

def is_balanced_curly(s, pos1, pos2):
  return is_balanced(s, '{', '}', pos1, pos2)

# Can pos2 see variables declared at pos1? (counting braces between is not
# sufficient as the visibility can be killed in between)
def from_to_scope(s, pos1, pos2):
  l = len(s)
  assert(pos1 >= 0)
  assert(pos1 < pos2)
  assert(pos2 < l)
  cnt = 0
  for i in range(pos1, pos2 + 1):
    if s[i] == '{':
      cnt += 1
    elif s[i] == '}':
      cnt -= 1
    if cnt == -1:
      return False
  return True

### Check if string ln contains string s
def contains(ln, s):
  ret = ln.find(s, 0)
  if ret != -1:
    return True
  return False

### Check if string ln contains string s, and s is delimited by special chars.
# A string at the beginning or end of line is delimited by definition.
def contains_delim(ln, s):
  l = len(s)
  ret = ln.find(s, 0)
  if ret != -1:
    if ret > 0 and ret + l < len(ln):
      return not ln[ret-1].isalnum() and not ln[ret+l].isalnum()
  return False

### Check if line has a statement keyword like if, while, ...
def contains_stat(ln):
  b = contains_delim(ln, "if")
  b = b or contains_delim(ln, "while")
  b = b or contains_delim(ln, "for")
  b = b or contains_delim(ln, "do")
  b = b or contains_delim(ln, "switch")
  b = b or contains_delim(ln, "case")
  return b

### Check if string contains carriage returns
def check(s):
  mo = re.search('\r', s)
  if mo == None:
    return True
  return False

def is_stat_delim(c):
  return c == ';' or c == '{' or c == '}'

# ------------------------------------------------------------------------------
# Fix braces in string

### Fix statements other than cases
# s: whole source
def fix(s):
  pat = '([;}\t\n ](if|while|for))|(do[\t\n ]*\{)'

  s_prev = s

  # Set of starting locations of whiles that belong to previous do's
  forbidden = set()

  while True:
    locs = []
    it = re.finditer(pat, s)

    # For all match objects
    for mo in it:
      pos = mo.start()

      # Ignore lines that are defines or comments (check for not equal to \n to
      # avoid skipping to the previous line)
      if s[pos] != '\n':
        px = ln_tos(s, pos)
        px = eat(s, px)
        if s[px] == '#':
          continue
        if s[px:px+2] == '//':
          continue
        if s[px:px+2] == '/*':
          continue

      if s[pos:pos+2] == 'do':
        pos += 2
        pos = eat(s, pos)
        assert(s[pos] == '{')
        pos = skip_b(s, pos)
        pos = eat(s, pos)
        assert(s[pos:pos+5] == 'while')
        forbidden.add(pos)
        continue

      pos += 1

      # While that belongs to a previous do
      if pos in forbidden:
        continue

      pos = skip_stat(s, pos)

      # Spurious statement
      if pos == -1:
        continue

      if s[pos] == '{':
        # Already wrapped, nothing to do
        pass
      else:
        ppos = puke(s, pos - 1)
        ppos += 1
        # Try to skip statement below
        npos = skip_stat(s, pos)
        if npos == -1:
          # Statement ending in semicolon
          end = next_semicolon(s, pos)
          assert(end > 0)
          locs.append((ppos, '{'))
          locs.append((end + 1, '}'))
        elif s[npos] == '{':
          # Wrapped statement
          end = skip_b(s, npos)
          locs.append((ppos, '{'))
          locs.append((end, '}'))

    s = insert_items(s, locs)
    if (s == s_prev):
      break
    s_prev = s

  return s

### Wrap cases in switch statement in curly braces
# s: whole source
def fix_case(s):
  pat = '([\t ]((case[^:\n]+\:)|(default\:))|(switch[ \t]*\())'
  it = re.finditer(pat, s)
  locs = []
  prev_end = -1

  for mo in it:
    pos = mo.start()
    if s[pos:pos+6] == 'switch':
      prev_end = -1
    else:
      start = mo.start()
      if prev_end != -1 and is_balanced_curly(s, prev_end, start):
        locs.append((prev_end, '{'))
        locs.append((start, '}'))
      prev_end = mo.end()

  s = insert_items(s, locs)
  return s

# ------------------------------------------------------------------------------
# Dependency handling (ARM only)

### Connect a read via a dependency to a previous read
# s: file as string
# pos: points at newline at end of line
# cv: name of the connecting variable
# read_exp: expression that corresponds to the read
# return value:
#   1: true if connected, false otherwise
#   2: transformed string
def connect_rd_dp(s, pos, cv, read_exp):
  repl = "*(&(" + read_exp + ")" + cv + ")"
  s = replace_ln(s, pos, read_exp, repl)
  return s

# Connect a write via a dependency to a previous read
# s: file as string
# pos: points at newline at end of line
# cv: name of the connecting variable
# return value: 
#   1: true if connected, false otherwise
#   2: transformed string
def connect_wrt_dp(s, pos, cv):
  # Find pattern " = " (matches practically all writes occuring in a C program)
  pos -= 1
  while pos >= 0 and s[pos] != '\n':
    if s[pos] == '=' and s[pos-1] == ' ' and s[pos+1] == ' ':
      s = insert(s, pos + 2, cv + " + ")
      return True, s
    pos -= 1
  return False, s

# ------------------------------------------------------------------------------
# Temporary variable names

### Get name of next temporary variable
tmp_cnt = 0
def next_tmp():
  global tmp_cnt
  tmp_cnt += 1
  vn = 'tmp_xjsdfk_' + str(tmp_cnt)
  return vn

### Get name of next pull temporary variable
tmp_cnt_pull = 0
def next_tmp_pull():
  global tmp_cnt_pull
  tmp_cnt_pull += 1
  vn = 'tmp_pull_' + str(tmp_cnt_pull)
  return vn

### Get name of next connection temporary variable
tmp_cnt_con = 0
def next_tmp_con():
  global tmp_cnt_con
  tmp_cnt_con += 1
  vn = 'tmp_con_' + str(tmp_cnt_con)
  return vn

# ------------------------------------------------------------------------------

### Insert given statement at given position (for inserting full fences).
# s: file as string
# pos: points at newline character at end of line
# asm: asm statement to insert
# line_cnt: line in results.txt
placement_cnt = 0
def place_fence(s, pos, asm, line_cnt):
  assert(s[pos] == '\n')

  global placement_cnt
  placement_cnt += 1
  pc = str(placement_cnt)

  # Check if it's an if or while at the end of the line
  pn = puke(s, pos)
  if s[pn] == '{':
    pn = puke(s, pn - 1)
  if s[pn] == ')':
    pb = skip_p_b(s, pn) + 1
    assert(s[pb] == '(')
    # Condition including parentheses
    cond = s[pb:pn+1]
    p = puke(s, pb - 1)
    if s[p-1:p+1] == 'if':
      px = puke(s, p-2)
      if re.search('[;}\t\n ]', s[p-2]) != None and s[px-3:px+1] != 'else':
        # We have found a suitable if
        tmp = next_tmp()
        s = delete(s, pb + 1, pn)
        s = insert(s, pb + 1, tmp)
        p -= 1
        s = insert(s, p, 'long ' + tmp + ' = (long)' + cond + ';' + asm)
        print('Placing fence ' + line_cnt + ' with rule 1')
        return s
    elif s[p-4:p+1] == 'while':
      if re.search('[;}\t\n ]', s[p-5]) != None:

        tmp = next_tmp()
        pulled = tmp + ' = (long)' + cond + ';' + asm

        # Statement at end of while loop
        idx = next_item(s, p, '{')
        assert(s[idx] == '{')
        idx = skip_b(s, idx)
        idx -= 1
        assert(s[idx] == '}')
        s = insert(s, idx, pulled)
        
        pulled = 'long ' + pulled
        s = delete(s, pb + 1, pn)
        s = insert(s, pb + 1, tmp)
        p -= 4
        s = insert(s, p, pulled)
        print('Placing fence ' + line_cnt + ' with rule 2')
        return s

  # Try to place on same line (at the end)
  pn = puke(s, pos)
  while s[pn] == '}':
    pn = puke(s, pn - 1)
  c = s[pn]
  if c == ';' or c == '{':
    s = insert(s, pn + 1, asm)
    print('Placing fence ' + line_cnt + ' with rule 3')
    return s

  # Try to place on next line (at the beginning)
  pn = eat(s, pos)
  c = s[pn]
  if c == '{':
    s = insert(s, pn + 1, asm)
    print('Placing fence ' + line_cnt + ' with rule 4')
    return s

  print('Ignoring fence ' + line_cnt)
  return s

# ------------------------------------------------------------------------------

### Get asm statement connecting a read with a read/write
# inv: in variable
# outv: out variable
def get_connector(inv, outv):
  s = "__asm volatile(\"eors %0, %1, %1\" : \"=r\"(" + outv + ") : \"r\"(" + \
      inv + "));"
  return s

### Connect an expression expr via connection variable cv
# Works for both read and write targets
# s:
# pos: starting index of the expression
# cv: connection variable
# expr: original expression
def connect_dp(s, pos, cv, expr):
  repl = "(*(&(" + expr + ") + " + cv + "))"
  s = replace_ln(s, pos, expr, repl)
  return s

### Place the asm connection statement
# s:
# idx: index of the second expression belonging to the dependency
# ps: index of the start of the line
# asm_st: asm statement to place
def place_asm_st(s, idx, ps, asm_st):
  assert(idx > ps)
  pt = puke2(s, idx-1)
  tc = s[pt]
  if is_stat_delim(tc):
    # Place immediately before the expression
    s = insert(s, pt+1, asm_st)
    return s
  else:
    pt = puke(s, ps-1)
    tc = s[pt]
    if is_stat_delim(tc):
      # Place at start of line
      assert(s[ps] != '\n')
      s = insert(s, ps, asm_st)
      return s
    else:
      # Connector asm statement cannot be placed
      return ""

### Add a dependency between the accesses
# s: file as string
# pos1: points at newline character at end of line of first access
# pos2: points at newline character at end of line of second access
# fst: first expression (read)
# snd: second expression (read or write)
# ty: type of first expression
# line_cnt: corresponding line number in results.txt
def place_dp(s, pos1, pos2, fst, snd, ty, line_cnt):

  if ty == '' or ty == ' ':
    return s

  # Strip off c:: from source and target expressions (if any)
  if fst[0:3] == 'c::':
    fst = fst[3:]  

  if snd[0:3] == 'c::':
    snd = snd[3:]

  ps1 = ln_etos(s, pos1)
  ps2 = ln_etos(s, pos2)
  assert(ps1 != '\n')
  assert(ps2 != '\n')

  ln1 = extract_ln(s, pos1)
  ln2 = extract_ln(s, pos2)

  # Check if expressions exist on line (exact matches)
  if not contains(ln1, fst):
    print('dp ' + line_cnt + ', first expression not found')
    return s
  if not contains(ln2, snd):
    print('dp ' + line_cnt + ', second expression not found')
    return s

  # Get starting indices of expressions in source file
  idx1 = s.find(fst, ps1)
  idx2 = s.find(snd, ps2)
  assert(idx1 != -1)
  assert(idx2 != -1)
  len1 = len(fst)
  len2 = len(snd)

  if not from_to_scope(s, idx1, idx2):
    print('dp ' + line_cnt + ', target out of scope')
    return s

  # At this point, we're pretty confident that it's possible to insert the dep
  # :-)

  # Handle source of dependency
  stat = contains_stat(ln1)
  if stat:
    # Source line contains a complicated statement (if, while, for, do, case,
    # switch)
    print('Inserting dependency with complicated source, ' + line_cnt)

    # Handle target of dependency
    sn = connect_dp(s, idx2, "0", snd)
    assert(len(sn) > 0)

    # Handle connector asm statement
    asm_st = '__asm volatile("":::"memory");'
    sn = place_asm_st(sn, idx2, ps2, asm_st)
    if sn == '':
      return s
  else:
    # Source line is simple
    print('Inserting dependency with simple source, ' + line_cnt)

    # Pull and connection variables
    pv = next_tmp_pull()
    con = next_tmp_con()

    # Handle target of dependency
    sn = connect_dp(s, idx2, con, snd)
    assert(len(sn) > 0)

    # Handle connector asm statement
    asm_st = get_connector(pv, con)
    sn = place_asm_st(sn, idx2, ps2, asm_st)
    if sn == '':
      return s

    # Transform line to pulled version
    sn = delete(sn, idx1, idx1 + len1)
    sn = insert(sn, idx1, '(' + pv + ')')
    con_and_pull = 'int ' + con + ' = 0; ' + ty + ' ' + pv + ' = ' + fst + ';'
    while True:
      idx1 -= 1
      c = sn[idx1]
      if c == ';' or c == '{' or c == '}' or c == '\n':
        sn = insert(sn, idx1 + 1, con_and_pull)
        break

  return sn

# ------------------------------------------------------------------------------

# Process each line in results.txt separately; not efficient but OK ...
# fences: list of pairs (with pair = (num, list), a list in a pair represents a
# line in results.txt)
#
# fences: all non-ignored lines in results.txt
def insert_fences(fences):
  global musk_form
  global handle_dp
  global fm

  # For every line in results.txt
  for p in fences:
    line_cnt = str(p[0])
    l = p[1]

    # Read file into string
    assert(im_src_file1 == io_src_file)
    fn = l[im_src_file1]
    f = open(fn, 'r')
    s = f.read()
    f.close()

    # Sanity checks
    if musk_form:
      if l[im_src_file1] != l[im_src_file2]:
        print('Ignoring fence/dp ' + line_cnt + ', file mismatch')
        continue
      if l[im_func_name1] != l[im_func_name2]:
        print('Ignoring fence/dp ' + line_cnt + ', func mismatch')
        continue

    # Handle inverse line numbers
    if musk_form:
      if int(l[im_line1]) > int(l[im_line2]):
        pass

    place_full_fence = True

    # Dp's are handled specially and line specifies a dp
    if handle_dp and l[im_fence] == "dp":
      assert(musk_form)

      # Get position pointers
      ln1 = int(l[im_line1])
      ln2 = int(l[im_line2])
      if ln1 == ln2:
        print('Ignoring dp ' + line_cnt + ', same line numbers')
        continue
      pos1 = after_line(s, ln1)
      pos2 = after_line(s, ln2)

      # Expressions
      fst = l[im_exp1]
      snd = l[im_exp2]

      # Type of first expression (+ replace _ by space)
      ty = l[im_type1]
      ty = ty.replace('_', '')

      s_bak = s
      s = place_dp(s, pos1, pos2, fst, snd, ty, line_cnt)
      # Dependency successfully inserted
      if (s != s_bak):
        place_full_fence = False
    
    if place_full_fence:
      # Insert a normal fence
      assert(im_fence == io_fence)
      try:
        fence = fm[l[im_fence]]
      except KeyError:
        print_err('Unrecognized fence for architecture. Exiting.')
        sys.exit(1)

      # Using __asm as asm does not work with -std=c99
      asm = '__asm volatile ("' + fence + '":::"memory");'
      # Throws ValueError if not an integer
      if musk_form:
        if fence_pos == fence_first:
          ln = int(l[im_line1])
        elif fence_pos == fence_second:
          ln = int(l[im_line2])-1
      else:
        ln = int(l[io_line])

      # Point at newline character at end of line
      pos = after_line(s, ln)
      #assert(s[pos] == '\n')
      assert_msg(s[pos] == '\n', 'Insert at line: ' + str(ln) + ', File: ' + fn)

      s = place_fence(s, pos, asm, line_cnt)

    # Write back result
    f = open(fn, 'w')
    f.write(s)
    f.close()

# ------------------------------------------------------------------------------

def handle_args(args):
  global musk_form
  global handle_dp
  global fm

  if len(sys.argv) != 5:
    print_err('Number of arguments != 5\n')
    usage()
    sys.exit(1)

  arch = sys.argv[1]
  if arch == 'x86':
    print('x86 architecture')
    fm = fm_x86
  elif arch == 'arm':
    print('ARM architecture')
    fm = fm_arm
  else:
    print_err('Unrecognized architecture')
    sys.exit(1)

  dp_mode = sys.argv[2]
  if dp_mode == "dp":
    print('Handling dp')
    handle_dp = True
  elif dp_mode == "fence":
    print('Using full fence for dp')
    handle_dp = False
  else:
    print_err('Unrecognized fencing strategy')
    sys.exit(1)

  in_form = sys.argv[3]
  if in_form == "musk":
    print('Input format musketeer\n')
    musk_form = True
  elif in_form == "other":
    print('Input format other\n')
    musk_form = False
  else:
    print_err('Unrecognized format selector')
    sys.exit(1)

  if handle_dp and (not(musk_form) or not(arch == 'arm')):
    print_err('Incompatible argument values.')
    sys.exit(1)

# ------------------------------------------------------------------------------

if __name__ == "__main__":

  handle_args(sys.argv)
  # Hack (musk output insufficient for dp insertion at the moment)
  handle_dp = False

  print('Current working directory: \n' + os.getcwd() + '\n')

  # Read results file (check files mentioned in there)
  fences = [] # list of pairs: (num, list)
  files = [] # files in results.txt that will be fenced
  all_files = [] # all files mentioned in results.txt
  with open(sys.argv[4], 'r') as f:
    cnt = 0
    for line in f:
      cnt += 1
      # Note: "a||b|".split('|') yields ['a', '', 'b', '']
      l = line.split('|')
      cols = len(l)
      if cols == 11 or cols == 13:
        print('<results> is from older version of musketeer')
        sys.exit(1)
      assert(cols == 5 or cols == 9)
      assert(im_src_file1 == io_src_file)
      fn = l[im_src_file1]
      all_files.append(fn)
      if fn[0] != '/' and os.path.isfile(fn):
        # Files to fence
        files.append(fn)
        # Fencing instruction used (and its line in results.txt)
        fences.append((cnt, l))

  # Check if files exist before doing anything
  not_found = False
  all_files = list(set(all_files))
  for f in all_files:
    if not(os.path.isfile(f)):
      not_found = True
      print('File ' + f + ' does not exist')
      continue
    if f[0] == '/':
      not_found = True
      print('File ' + f + ' has absolute path. Ignoring.')

  # Print extra newline if there is a file we ignore (pretty printing)
  if not_found:
    print()

  # Files to fence
  files = list(set(files))

  # Backup files (if backup doesn't exist yet)
  for f in files:
    backup = f + '.fibak'
    if not(os.path.isfile(backup)):
      shutil.copyfile(f, backup)

  # Fix curly braces in files (results.txt is not used)
  for f in files:
    sf = open(f, 'r')
    s = sf.read()
    # Check if file contains carriage returns
    r = check(s)
    if not(r):
      print_err('File ' + f + ' contains carriage returns')
      sys.exit(1)
    sf.close()
    # Fix the cases of switch statements
    s = fix_case(s)
    # Fix the remaining statements
    s = fix(s)
    sf = open(f, 'w')
    sf.write(s)
    sf.close()

  # Do actual fence insertion (fences: list of pairs, with pair = (num, list),
  # with num denoting the line number of the entry in results.txt)
  insert_fences(fences)
  print('\ndone')

