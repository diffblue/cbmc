#!/usr/bin/env python3
"""Generate the declarations of GCC's AArch64 built-in functions.

GCC does not list its AArch64 builtins (__builtin_aarch64_*, the ACLE __arm_*
functions, and the intrinsics that GCC 13 and later register itself rather than
defining them in <arm_neon.h>) in any parseable form: their types are built
from mode and qualifier tables when the compiler starts up or when it processes
'#pragma GCC aarch64 "arm_neon.h"'.  This script therefore asks GCC for each
type.  It calls every candidate builtin with 0 to MAX_ARGS arguments of a
struct type: for the right number of arguments GCC reports the expected type
of each parameter.  A second pass assigns a call with arguments of those types
to a struct variable, which makes GCC report the return type.

Usage, with any number of AArch64 cross compilers (e.g. from Ubuntu's
gcc-N-aarch64-linux-gnu packages), oldest first:

    gcc_aarch64_builtins.py aarch64-linux-gnu-gcc-11 ... \
        aarch64-linux-gnu-gcc-16

The script writes two files to the current directory:

  gcc_builtin_headers_aarch64.h        declarations that CBMC's builtin_factory
                                       looks up on demand
  gcc_builtin_headers_aarch64_neon.h   the NEON tuple types and the builtins
                                       using them, which GCC 12 and later
                                       declare at '#pragma GCC aarch64
                                       "arm_neon.h"' (GCC 11 defines the tuple
                                       types in <arm_neon.h> and uses opaque
                                       types for those builtins instead)

Where compilers disagree on a signature the newest one wins, except that the
on-demand header keeps the GCC 11 signature of a builtin whose newer signature
uses a tuple type: CBMC only looks it up when no pragma declared it.
"""

import os
import re
import subprocess
import sys
import tempfile

HEADERS = ['arm_neon.h', 'arm_acle.h', 'arm_fp16.h', 'arm_bf16.h']
MAX_ARGS = 7

# Architecture versions and extensions to enable, so that GCC does not reject
# a call for lack of an ISA extension; each compiler gets the newest version
# and all extensions it accepts.
ARCHES = ['armv9.6-a', 'armv9.5-a', 'armv9.4-a', 'armv9.3-a', 'armv9-a',
          'armv8.6-a']
EXTENSIONS = ['crc', 'crypto', 'aes', 'sha2', 'sha3', 'sm4', 'fp16', 'fp16fml',
              'rcpc', 'rdma', 'dotprod', 'i8mm', 'bf16', 'memtag', 'rng',
              'tme', 'ls64', 'sve', 'sve2', 'f32mm', 'f64mm', 'flagm', 'pauth',
              'mops', 'cssc', 'd128', 'gcs', 'the', 'sme', 'sme2', 'fp8',
              'fp8dot2', 'fp8dot4', 'fp8fma', 'faminmax', 'lut', 'cmpbr',
              'f8f16mm', 'f8f32mm', 'sve-f16f32mm', 'sme-f8f16', 'sme-f8f32',
              'sve2p1', 'sme2p1', 'rcpc3', 'lse128']

TUPLE_RE = re.compile(r'^struct (\w+x\d+x[234]_t)$')


def compile_c(cc, args, source):
    """Run cc -fsyntax-only on source, returning (exit code, stderr)."""
    with tempfile.NamedTemporaryFile('w', suffix='.c', delete=False) as f:
        f.write(source)
        name = f.name
    try:
        p = subprocess.run([cc, '-fsyntax-only'] + args + [name],
                           capture_output=True, text=True,
                           env=dict(os.environ, LC_ALL='C'))
        return p.returncode, p.stderr
    finally:
        os.unlink(name)


def best_march(cc):
    for arch in ARCHES:
        if compile_c(cc, ['-march=' + arch], 'int x;\n')[0] == 0:
            break
    exts = []
    for e in EXTENSIONS:
        march = '-march=' + arch + ''.join('+' + x for x in exts + [e])
        if compile_c(cc, [march], 'int x;\n')[0] == 0:
            exts.append(e)
    return '-march=' + arch + ''.join('+' + x for x in exts)


def tool_output(cc, flag):
    return subprocess.run([cc, flag], capture_output=True,
                          text=True).stdout.strip()


def candidate_names(cc, march, prelude):
    """The __builtin_aarch64_* names in GCC's ACLE headers, before and after
    preprocessing (macros paste some of them together, others only appear in
    macro definitions), plus the intrinsic-like strings of cc1 that name
    builtins, i.e., the intrinsics that GCC registers itself."""
    inc = tool_output(cc, '-print-file-name=include')
    text = ''
    for h in sorted(os.listdir(inc)):
        if h.startswith('arm_') and h.endswith('.h'):
            with open(os.path.join(inc, h)) as f:
                text += f.read()
    p = subprocess.run([cc, '-E', march, '-x', 'c', '-'], input=prelude,
                       capture_output=True, text=True)
    names = set(re.findall(r'\b__builtin_aarch64_\w+', text + p.stdout))
    with open(tool_output(cc, '-print-prog-name=cc1'), 'rb') as f:
        data = f.read()
    strings = sorted(set(m.group(1).decode() for m in re.finditer(
        rb'(?<![\x21-\x7e])(v[a-z0-9_]+|__arm_[a-z0-9_]+)\x00', data)))
    # Redeclaring a builtin with another type is an error that, unlike for a
    # function that a header defines, refers to no previous declaration.
    base = 100000
    src = [prelude, 'struct __probe_s { int x; };\n']
    for i, name in enumerate(strings):
        src.append('#line %d\nvoid %s(struct __probe_s);\n' % (base + i, name))
    _, err = compile_c(cc, [march, '-fmax-errors=0'], ''.join(src))
    for (i, _), msgs in parse_diagnostics(err, base, 1).items():
        if any(msg.startswith("conflicting types for '") for _, msg in msgs) \
                and not any(kind == 'note' for kind, _ in msgs):
            names.add(strings[i])
    return sorted(names)


def parse_diagnostics(stderr, base, stride):
    """Group the diagnostics by the probe line they refer to: line
    base + i * stride + k is probe k of name i.  Notes belong to the
    preceding error."""
    result = {}
    current = None
    for line in stderr.splitlines():
        m = re.match(r'^[^:]+:(\d+):\d+: (error|warning|note): (.*)$', line)
        if not m:
            continue
        kind, msg = m.group(2), m.group(3)
        if kind != 'note':
            n = int(m.group(1))
            current = divmod(n - base, stride) if n >= base else None
        if current is not None:
            result.setdefault(current, []).append((kind, msg))
    return result


def probe_parameters(cc, march, names, prelude):
    """Return {name: [parameter types]} for those candidates that are
    functions."""
    stride = MAX_ARGS + 1
    base = 100000
    src = [prelude, 'struct __probe_s { int x; };\n',
           'void __probe(void) {\n struct __probe_s s;\n']
    for i, name in enumerate(names):
        for k in range(MAX_ARGS + 1):
            # each call in a block of its own: if a name turns out to be a
            # type, "T(s);" declares a new s
            src.append('#line %d\n { %s(%s); }\n' % (
                base + i * stride + k, name, ', '.join(['s'] * k)))
    src.append('}\n')
    _, err = compile_c(cc, [march, '-fmax-errors=0'], ''.join(src))
    diags = parse_diagnostics(err, base, stride)
    result = {}
    for i, name in enumerate(names):
        probes = [diags.get((i, k), []) for k in range(MAX_ARGS + 1)]
        if not any(probes):
            continue  # undeclared (implicit declarations are warnings)
        for k, msgs in enumerate(probes):
            text = ' '.join(msg for _, msg in msgs)
            if 'implicit declaration' in text:
                break  # a warning before GCC 14
            if 'too few arguments' in text or 'too many arguments' in text:
                continue
            if any(kind == 'error' and not msg.startswith(
                    'incompatible type for argument') for kind, msg in msgs):
                break  # e.g. undeclared or not a function
            types = {}
            argno = None
            for kind, msg in msgs:
                m = re.match(r"incompatible type for argument (\d+) of '", msg)
                if m:
                    argno = int(m.group(1))
                    continue
                m = re.match(r"expected '(.*)' but argument is of type '.*'$",
                             msg)
                if m and argno is not None:
                    types[argno] = m.group(1)
                    argno = None
            if len(types) == k:
                result[name] = [types[j] for j in range(1, k + 1)]
            else:
                sys.stderr.write('%s: cannot determine parameters\n' % name)
            break
    return result


INTEGER_TYPE_RE = re.compile(
    r'^((un)?signed |short |long )*(int|char|short|long)( (unsigned|int))*$')


def argument(t, j):
    """An argument of type t: integer constants, as some builtins demand
    constants, string literals, as some demand those, else variables."""
    if t == 'const char *':
        return '""'
    if INTEGER_TYPE_RE.match(t):
        return '0'
    return '__a%d' % j


def probe_return_types(cc, march, signatures, prelude):
    base = 100000
    names = sorted(signatures)
    src = [prelude, 'struct __probe_s { int x; };\n',
           'void __probe(void) {\n struct __probe_s s;\n']
    for i, name in enumerate(names):
        params = signatures[name]
        args = [argument(t, j) for j, t in enumerate(params)]
        decls = ''.join(
            ' %s __a%d;' % (re.sub(r'^const ', '', t), j)
            for j, t in enumerate(params) if args[j].startswith('__a'))
        src.append('#line %d\n {%s s = %s(%s); }\n' % (
            base + i, decls, name, ', '.join(args)))
    src.append('}\n')
    _, err = compile_c(cc, [march, '-fmax-errors=0'], ''.join(src))
    result = {}
    for (i, _), msgs in parse_diagnostics(err, base, 1).items():
        for kind, msg in msgs:
            m = re.match(r"incompatible types when assigning to type "
                         r"'struct __probe_s' from type '(.*)'$", msg)
            if m:
                result[names[i]] = m.group(1)
            elif 'void value not ignored' in msg or \
                    msg == 'invalid use of void expression':
                result[names[i]] = 'void'
    return result


def probe(cc):
    march = best_march(cc)
    prelude = ''.join('#include <%s>\n' % h for h in HEADERS)
    names = candidate_names(cc, march, prelude)
    # Drop the generic builtins (e.g. vfprintf) that cc1's strings include.
    generic = probe_parameters(cc, march, names, '')
    names = [n for n in names
             if n.startswith('__builtin_aarch64_') or n not in generic]
    params = probe_parameters(cc, march, names, prelude)
    returns = probe_return_types(cc, march, params, prelude)
    sigs = {}
    for name, p in params.items():
        if name in returns:
            sigs[name] = [returns[name]] + p
        else:
            sys.stderr.write('%s: cannot determine return type\n' % name)
    sys.stderr.write('%s (%s): %d builtins\n' % (cc, march, len(sigs)))
    return sigs


def c_type(t):
    """Spell a type as printed by GCC so that CBMC parses it regardless of
    the __fp16 and __bf16 keywords being enabled; CBMC models both as
    _Float16."""
    t = re.sub(r'\b(__fp16|__bf16)\b', '__CPROVER_Float16', t)
    t = re.sub(r'^__int128 unsigned\b', 'unsigned __int128', t)
    return t


def declaration(name, sig):
    params = ', '.join(c_type(t) for t in sig[1:]) or 'void'
    return '%s %s(%s);' % (c_type(sig[0]), name, params)


def uses_tuple(sig):
    return any(TUPLE_RE.match(t) for t in sig)


def main():
    compilers = sys.argv[1:]
    if not compilers:
        sys.exit(__doc__)
    newest = {}
    no_tuple = {}
    for cc in compilers:
        for name, sig in probe(cc).items():
            newest[name] = sig
            if not uses_tuple(sig):
                no_tuple[name] = sig

    versions = [tool_output(cc, '-dumpfullversion') for cc in compilers]
    generated = '// Generated by gcc_aarch64_builtins.py using GCC %s.\n' % \
        ', '.join(versions)

    tuples = sorted(set(
        TUPLE_RE.match(t).group(1)
        for sig in newest.values() for t in sig if TUPLE_RE.match(t)))

    with open('gcc_builtin_headers_aarch64.h', 'w') as f:
        f.write('// clang-format off\n' + generated)
        for name in sorted(newest):
            sig = newest[name] if not uses_tuple(newest[name]) \
                else no_tuple.get(name)
            if sig:
                f.write(declaration(name, sig) + '\n')
        f.write('// clang-format on\n')

    with open('gcc_builtin_headers_aarch64_neon.h', 'w') as f:
        f.write('// clang-format off\n' + generated)
        for t in tuples:
            m = re.match(r'^([a-z]+)(\d+)x(\d+)x([234])_t$', t)
            element = '__' + m.group(1).capitalize() + m.group(2) + 'x' + \
                m.group(3) + '_t'
            f.write('typedef struct %s { %s val[%s]; } %s;\n' % (
                t, element, m.group(4), t))
        for name in sorted(newest):
            if uses_tuple(newest[name]):
                f.write(declaration(name, newest[name]) + '\n')
        f.write('// clang-format on\n')


if __name__ == '__main__':
    main()
