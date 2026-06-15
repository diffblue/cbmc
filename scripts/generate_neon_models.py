#!/usr/bin/env python3
#
# Draft generator for ARM/AArch64 NEON CBMC library models.
#
# Two-source design:
#
#  * Structure comes from Clang's arm_neon.td: which builtins exist, the
#    element types each supports, and -- since Clang's NEON builtins are
#    polymorphic -- the NeonTypeFlags type code that selects the lane type at
#    each call site.  An intrinsic defined with an *OpInst class is open-coded
#    by <arm_neon.h> into native C operators, so it needs no model and is
#    skipped here; only the opaque SInst/IInst/... builtins are modelled.
#
#  * Semantics come from OP_TABLE below.  arm_neon.td carries no semantics
#    the opaque builtins (the Operation field is OP_NONE), so the per-lane
#    computation is supplied here.  For the mechanically-translatable ops
#    (min/max/absolute-difference/...) the body is obvious from the operation
#    and is encoded directly.  The non-trivial ops (saturating, rounding,
#    narrowing, floating-point estimate, table, crypto, ...) need real
#    pseudocode -- ultimately from ARM's machine-readable spec -- and are
#    reported as unmodelled rather than guessed at.
#
# The emitted models match the declarations in gcc_builtin_headers_aarch64.h:
# every operand is the byte-representative lane type (__gcc_v16qi for 128-bit,
# __gcc_v8qi for 64-bit) plus an int type code, exactly as <arm_neon.h> calls
# them.

import argparse
import re
import shutil
import subprocess
import sys

# NeonTypeFlags element-type enum (clang/Basic/TargetBuiltins.h) for the
# base types we model, plus the lane bit width.  The full integer type code is
#   EltType | (unsigned ? 0x10 : 0) | (quad ? 0x20 : 0)
INT_BASE = {
        'c': ('Int8', 0, 8),
        's': ('Int16', 1, 16),
        'i': ('Int32', 2, 32),
        'l': ('Int64', 3, 64),
        }
UNSIGNED_FLAG = 0x10
QUAD_FLAG = 0x20

# gcc vector typedef stem for a lane width (see gcc_builtin_headers_types).
STEM = {8: 'qi', 16: 'hi', 32: 'si', 64: 'di'}
# scalar C type for a lane.
SCALAR = {
        (8, False): 'signed char', (8, True): 'unsigned char',
        (16, False): 'short', (16, True): 'unsigned short',
        (32, False): 'int', (32, True): 'unsigned int',
        (64, False): 'long long', (64, True): 'unsigned long long',
        }
# next wider *signed* type, used to compute a signed difference without
# overflow.
WIDER = {8: 'int', 16: 'int', 32: 'long long', 64: '__int128'}


def sat_bounds(signed, width):
    """Return (lo, hi) C integer literals for a lane's saturation range."""
    if signed:
        hi = 2 ** (width - 1) - 1
        if width == 64:
            return '(-{}LL - 1)'.format(hi), '{}LL'.format(hi)
        return str(-2 ** (width - 1)), str(hi)
    hi = 2 ** width - 1
    if width == 64:
        return '0', '{}ULL'.format(hi)
    return '0', str(hi)


def lane_body(op, signed, width):
    """Return the loop body computing r[i] from x[i], y[i] for one lane, for an
    element-wise (non-reshaping) operation.  Signed arithmetic is widened to
    avoid signed-overflow undefined behaviour."""
    wide = WIDER[width]
    if op == 'vmax':
        return 'r[i] = x[i] > y[i] ? x[i] : y[i];'
    if op == 'vmin':
        return 'r[i] = x[i] < y[i] ? x[i] : y[i];'
    if op == 'vabd':
        if signed:
            return ('{{ {w} d = ({w})x[i] - ({w})y[i]; '
                    'r[i] = d < 0 ? -d : d; }}').format(w=wide)
        return 'r[i] = x[i] > y[i] ? x[i] - y[i] : y[i] - x[i];'
    if op == 'vhadd':  # halving add: floor((a + b) / 2)
        return 'r[i] = (({w})x[i] + ({w})y[i]) >> 1;'.format(w=wide)
    if op == 'vhsub':  # halving subtract
        return 'r[i] = (({w})x[i] - ({w})y[i]) >> 1;'.format(w=wide)
    if op == 'vrhadd':  # rounding halving add: floor((a + b + 1) / 2)
        return 'r[i] = (({w})x[i] + ({w})y[i] + 1) >> 1;'.format(w=wide)
    if op == 'vqadd':  # saturating add
        lo, hi = sat_bounds(signed, width)
        if width == 64 and signed:
            # avoid __int128 (rejected by -pedantic): detect overflow on the
            # wrapped sum instead of widening.
            return (
                '{{ long long s = (long long)('
                '(unsigned long long)x[i] + (unsigned long long)y[i]); '
                'r[i] = ((x[i] ^ s) & (y[i] ^ s)) < 0 '
                '? (x[i] < 0 ? {lo} : {hi}) : s; }}').format(lo=lo, hi=hi)
        if width == 64:
            return ('{{ unsigned long long s = x[i] + y[i]; '
                    'r[i] = s < x[i] ? {hi} : s; }}').format(hi=hi)
        if signed:
            return ('{{ {w} s = ({w})x[i] + ({w})y[i]; '
                    'r[i] = s < {lo} ? {lo} : (s > {hi} ? {hi} : s); }}'
                    ).format(w=wide, lo=lo, hi=hi)
        return ('{{ {w} s = ({w})x[i] + ({w})y[i]; '
                'r[i] = s > {hi} ? {hi} : s; }}').format(w=wide, hi=hi)
    if op == 'vqsub':  # saturating subtract
        lo, hi = sat_bounds(signed, width)
        if not signed:
            return 'r[i] = x[i] > y[i] ? x[i] - y[i] : 0;'
        if width == 64:
            return ('{{ long long d = (long long)((unsigned long long)x[i] '
                    '- (unsigned long long)y[i]); '
                    'r[i] = ((x[i] ^ y[i]) & (x[i] ^ d)) < 0 '
                    '? (x[i] < 0 ? {lo} : {hi}) : d; }}').format(lo=lo, hi=hi)
        return ('{{ {w} s = ({w})x[i] - ({w})y[i]; '
                'r[i] = s < {lo} ? {lo} : (s > {hi} ? {hi} : s); }}'
                ).format(w=wide, lo=lo, hi=hi)
    if op == 'vtst':  # test bits: all-ones per lane where (a & b) != 0
        return 'r[i] = (x[i] & y[i]) != 0 ? -1 : 0;'
    raise KeyError(op)


def pair_reduce(op, signed, width, p, q):
    """Return an expression combining two adjacent lanes p, q for a pairwise
    (reshaping) operation."""
    if op == 'vpmax':
        return '{p} > {q} ? {p} : {q}'.format(p=p, q=q)
    if op == 'vpmin':
        return '{p} < {q} ? {p} : {q}'.format(p=p, q=q)
    if op == 'vpadd':  # modular add; compute unsigned to avoid overflow UB
        u = SCALAR[(width, True)]
        return '({u}){p} + ({u}){q}'.format(u=u, p=p, q=q)
    raise KeyError(op)


# Element-wise opaque builtins we can model directly (one lane in, one out).
OP_TABLE = {'vabd', 'vmax', 'vmin', 'vqadd', 'vqsub', 'vhadd', 'vhsub',
            'vrhadd', 'vtst'}
# Pairwise opaque builtins (reduce adjacent lane pairs, concatenating a, b).
PAIRWISE = {'vpadd', 'vpmax', 'vpmin'}
# Bitwise-select: r = (mask & a) | (~mask & b); bit-level, so type-independent.
BITSELECT = {'vbsl'}
MODELLED = OP_TABLE | PAIRWISE | BITSELECT

# AArch64 instruction mnemonic (from ACLE advsimd.md) -> operation kind.  The
# instruction mnemonic is the authoritative semantic identity of an intrinsic;
# this compact table is the hand-written "semantics" source (see
# doc/neon-intrinsic-models.md).  Extend it (and MODELLED / lane_body /
# pair_reduce) to cover more instruction families.
INSTR_TABLE = {
        'SABD': 'vabd', 'UABD': 'vabd',
        'SMAX': 'vmax', 'UMAX': 'vmax',
        'SMIN': 'vmin', 'UMIN': 'vmin',
        'SQADD': 'vqadd', 'UQADD': 'vqadd',
        'SQSUB': 'vqsub', 'UQSUB': 'vqsub',
        'SHADD': 'vhadd', 'UHADD': 'vhadd',
        'SHSUB': 'vhsub', 'UHSUB': 'vhsub',
        'SRHADD': 'vrhadd', 'URHADD': 'vrhadd',
        'ADDP': 'vpadd',
        'SMAXP': 'vpmax', 'UMAXP': 'vpmax',
        'SMINP': 'vpmin', 'UMINP': 'vpmin',
        'CMTST': 'vtst',
        'BSL': 'vbsl',
        }


def typed_intrinsic(base, width, unsigned, quad):
    """Reconstruct the ACLE typed-intrinsic name, e.g. ('vabd', 8, False, True)
    -> 'vabdq_s8'."""
    suffix = ('u' if unsigned else 's') + str(width)
    return base + ('q' if quad else '') + '_' + suffix


ACLE_NAME_RE = re.compile(r'intrinsics/(\w+)"')
ACLE_MNEM_RE = re.compile(r'`([A-Z][A-Z0-9]+)\b')


def parse_acle(md_text):
    """Parse ARM's ACLE neon_intrinsics/advsimd.md into {intrinsic: mnemonic}.
    Each intrinsic is a markdown table row carrying a link to its guide page
    and the AArch64 instruction in backticks."""
    mapping = {}
    for line in md_text.splitlines():
        if '<code>' not in line:
            continue
        nm = ACLE_NAME_RE.search(line)
        if not nm:
            continue
        mn = ACLE_MNEM_RE.search(line)
        mapping[nm.group(1)] = mn.group(1) if mn else None
    return mapping


def parse_typespec(typespec):
    """Yield (base_char, unsigned, quad, other) for each type in a typespec,
    e.g. 'csiUcQUs' -> Int8, Int16, Int32, uInt8, quad-uInt16.  'other' is set
    when a modifier we do not model is present (S scalar, P poly, ...), so the
    caller can skip those variants -- they belong to different builtins."""
    i = 0
    while i < len(typespec):
        unsigned = quad = other = False
        while typespec[i].isupper():
            if typespec[i] == 'U':
                unsigned = True
            elif typespec[i] == 'Q':
                quad = True
            else:
                other = True
            i += 1
        yield typespec[i], unsigned, quad, other
        i += 1


INST_RE = re.compile(
        r'def\s+\w+\s*:\s*([A-Za-z]*Inst)<\s*"([^"]+)"\s*,\s*"[^"]*"\s*,'
        r'\s*"([^"]+)"')


def collect(td_text):
    """Return {builtin_name: [(code, width, unsigned), ...]} for the modelled
    ops, plus a sorted list of intrinsic names skipped for want of
    semantics."""
    builtins = {}
    skipped = set()
    for m in INST_RE.finditer(td_text):
        cls, name, typespec = m.group(1), m.group(2), m.group(3)
        if cls.endswith('OpInst'):
            continue  # open-coded -> native operators, no model needed
        if name not in MODELLED:
            skipped.add(name)
            continue
        for base, unsigned, quad, other in parse_typespec(typespec):
            if other or base not in INT_BASE:
                continue  # scalar/poly/float: not a plain integer vector
            _, elt_enum, width = INT_BASE[base]
            code = elt_enum | (UNSIGNED_FLAG if unsigned else 0) | \
                (QUAD_FLAG if quad else 0)
            builtin = '__builtin_neon_' + name + ('q' if quad else '') + '_v'
            # de-duplicate by type code: several .td records may map to the
            # same polymorphic builtin (e.g. scalar variants), and a switch
            # cannot repeat a case label.
            builtins.setdefault(builtin, {})[code] = (width, unsigned)
    models = {b: [(c, w, u) for c, (w, u) in sorted(d.items())]
              for b, d in builtins.items()}
    return models, sorted(skipped)


def emit_model(builtin, cases, acle=None):
    """Emit one /* FUNCTION */ block.  cases is a list of (code, width,
    unsigned); all share the same total width (64- or 128-bit).  If an ACLE
    {intrinsic: mnemonic} map is given, annotate the model with the
    authoritative instruction mnemonic(s) for provenance."""
    op = builtin[len('__builtin_neon_'):].rstrip('_v').rstrip('q')
    quad = builtin.endswith('q_v')
    total_bytes = 16 if quad else 8
    rep = '__gcc_v{}qi'.format(total_bytes)

    mnemonics = []
    if acle is not None:
        for _, width, unsigned in sorted(cases):
            mn = acle.get(typed_intrinsic(op, width, unsigned, quad))
            if mn and mn not in mnemonics:
                mnemonics.append(mn)

    if op in BITSELECT:
        # Bitwise select operates on the raw bits, so it is independent of the
        # lane type code: r = (mask & a) | (~mask & b).
        out = ['/* FUNCTION: {} */'.format(builtin), '']
        if mnemonics:
            out.append(
                '// Arm instruction(s): {} (per ACLE advsimd.md)'.format(
                    ', '.join(mnemonics)))
            out.append('')
        out.append(
            'typedef char {} __attribute__((__vector_size__({})));'.format(
                rep, total_bytes))
        out.append('')
        out.append('{rep} {b}({rep} mask, {rep} a, {rep} b, int type)'.format(
            rep=rep, b=builtin))
        out.append('{')
        out.append('  (void)type;')
        out.append('  return (mask & a) | (~mask & b);')
        out.append('}')
        return '\n'.join(out)

    # Collect the lane typedefs we need.
    typedefs = ['typedef char {} __attribute__((__vector_size__({})));'.format(
        rep, total_bytes)]
    seen = {rep}
    body_cases = []
    for code, width, unsigned in sorted(cases):
        lanes = total_bytes * 8 // width
        suffix = 'u' if unsigned else 's'
        lane_t = '__gcc_v{}{}_{}'.format(lanes, STEM[width], suffix)
        if lane_t not in seen:
            typedefs.append(
                'typedef {} {} __attribute__((__vector_size__({})));'.format(
                    SCALAR[(width, unsigned)], lane_t, total_bytes))
            seen.add(lane_t)
        if op in PAIRWISE:
            rx = pair_reduce(op, not unsigned, width,
                             'x[2 * i]', 'x[2 * i + 1]')
            ry = pair_reduce(op, not unsigned, width,
                             'y[2 * i]', 'y[2 * i + 1]')
            body_cases.append(
                '  case {code}:\n'
                '  {{\n'
                '    {t} x = ({t})a, y = ({t})b, r;\n'
                '    int h = {n} / 2;\n'
                '    for(int i = 0; i < h; i++)\n'
                '      r[i] = {rx};\n'
                '    for(int i = 0; i < h; i++)\n'
                '      r[h + i] = {ry};\n'
                '    return ({rep})r;\n'
                '  }}'.format(code=code, t=lane_t, n=lanes, rx=rx, ry=ry,
                             rep=rep))
        else:
            body = lane_body(op, not unsigned, width)
            body_cases.append(
                '  case {}:\n'
                '  {{\n'
                '    {t} x = ({t})a, y = ({t})b, r;\n'
                '    for(int i = 0; i < {n}; i++)\n'
                '      {body}\n'
                '    return ({rep})r;\n'
                '  }}'.format(code, t=lane_t, n=lanes, body=body, rep=rep))

    out = ['/* FUNCTION: {} */'.format(builtin), '']
    if mnemonics:
        out.append(
            '// Arm instruction(s): {} (per ACLE advsimd.md)'.format(
                ', '.join(mnemonics)))
        out.append('')
    out += typedefs
    out.append('')
    out.append(
        '{rep} {b}({rep} a, {rep} b, int type)'.format(rep=rep, b=builtin))
    out.append('{')
    out.append('  switch(type)')
    out.append('  {')
    out += body_cases
    out.append('  }')
    out.append('')
    out.append('  {} r = {{0}};'.format(rep))
    out.append('  return r;')
    out.append('}')
    return '\n'.join(out)


def audit(td_text, acle):
    """Report, over the opaque (model-needing) builtins, how the ACLE
    instruction mnemonics distribute and how far INSTR_TABLE covers them -- the
    modeling roadmap."""
    import collections
    covered = collections.Counter()
    todo = collections.Counter()
    for m in INST_RE.finditer(td_text):
        cls, name, typespec = m.group(1), m.group(2), m.group(3)
        if cls.endswith('OpInst'):
            continue
        for base, unsigned, quad, other in parse_typespec(typespec):
            if other or base not in INT_BASE:
                continue
            _, _, width = INT_BASE[base]
            mn = acle.get(typed_intrinsic(name, width, unsigned, quad))
            if mn is None:
                continue
            (covered if mn in INSTR_TABLE else todo)[mn] += 1
    sys.stderr.write(
        'ACLE audit: {} integer opaque-builtin lane-variants map to mnemonics '
        'INSTR_TABLE covers; {} do not yet.\n'.format(
            sum(covered.values()), sum(todo.values())))
    sys.stderr.write('  covered mnemonics: {}\n'.format(
        ', '.join('{}={}'.format(k, v) for k, v in covered.most_common())))
    sys.stderr.write('  top uncovered (modeling roadmap): {}\n'.format(
        ', '.join('{}={}'.format(k, v) for k, v in todo.most_common(15))))


def format_output(text):
    """Run the generated C through clang-format so it matches the project style
    (and the CI clang-format check), keeping regeneration idempotent. A no-op
    on already-clean output; if clang-format is unavailable the text is left
    unchanged."""
    for clang_format in ('clang-format-15', 'clang-format'):
        if shutil.which(clang_format):
            result = subprocess.run(
                [clang_format, '--assume-filename', 'arm_neon.c'],
                input=text, capture_output=True, text=True)
            if result.returncode == 0:
                return result.stdout
            break
    sys.stderr.write(
        'warning: clang-format not found; output left unformatted\n')
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('arm_neon_td', help='path to clang arm_neon.td')
    parser.add_argument(
        '--acle', metavar='ADVSIMD_MD',
        help='path to ARM ACLE neon_intrinsics/advsimd.md; keys semantics on '
             'the authoritative instruction mnemonic and annotates provenance')
    parser.add_argument(
        '-o', '--output', help='output .c file (default: stdout)')
    args = parser.parse_args()

    with open(args.arm_neon_td) as f:
        td_text = f.read()
    builtins, skipped = collect(td_text)

    acle = None
    if args.acle:
        with open(args.acle) as f:
            acle = parse_acle(f.read())

    blocks = [emit_model(b, cases, acle)
              for b, cases in sorted(builtins.items())]
    text = format_output('\n\n'.join(blocks) + '\n')

    if args.output:
        with open(args.output, 'w') as f:
            f.write(text)
    else:
        sys.stdout.write(text)

    sys.stderr.write(
        'generated {} model(s) for {} op(s); {} other opaque intrinsic(s) '
        'need ARM-sourced semantics\n'.format(
            len(builtins), len(MODELLED), len(skipped)))
    if acle is not None:
        audit(td_text, acle)


if __name__ == '__main__':
    main()
