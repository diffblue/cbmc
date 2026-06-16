#!/usr/bin/env python3
"""
Generate CBMC library models for x86 SIMD intrinsics.

Models are described by the curated MODELS table below -- one entry per Intel
_mm_* intrinsic, giving the element type, lane count, per-lane body and (where
applicable) signedness, shift parameter, equivalence oracle and AVX-512 mask
type. Wider-vector (AVX2 256-bit, AVX-512 512-bit) and merge-masked variants
are derived automatically from the 128-bit base entries. Each model is emitted
as a CBMC library function keyed by its GCC __builtin_ia32_* name, and the tool
cross-checks against the __builtin_ia32_* declarations shipped in CBMC's
compiler headers (src/ansi-c/compiler_headers/gcc_builtin_headers_ia32*.h) so
that it only emits models for builtins CBMC actually knows about.

The MODELS table is the authoritative, human-reviewed source of truth. The XML
modes below are *maintainer aids* for extending it; they never feed the
committed library directly.

Modes
-----
  -o FILE
      (Re)generate the library models into FILE (normally
      src/ansi-c/library/x86_intrinsics.c). Output is piped through
      clang-format-15 so regeneration is idempotent. CI re-runs this and
      diffs the result via scripts/check_intrinsic_models_sync.sh, so the
      committed file must always match the generator.

  --status
      Print a coverage report: which declared __builtin_ia32_* builtins are
      modeled, grouped by CPUID feature. Use this to see what is left to do.

  --status --xml data-latest.xml
      As --status, plus a survey of which not-yet-modeled builtins have an
      <operation> in Intel's Intrinsics Guide XML that is simple enough for the
      --emit-drafts translator to handle (see below). Helps pick the next
      tractable batch to model.

  --emit-drafts data-latest.xml
      Maintainer aid for growing the MODELS table. Translates the simple
      element-wise pseudocode of not-yet-modeled intrinsics (see
      parse_operation() for the exact accepted shape) into *draft* Model()
      entries printed to stdout for review, and self-checks the translator by
      re-deriving the geometry of the hand-written models and reporting any
      mismatch. The drafts are intentionally incomplete: the translator does
      NOT infer signedness or apply the UB-hardening (unsigned wrapping
      arithmetic, modular negation) that correct models need, so a human must
      finish and move each draft into MODELS. Nothing is written to the
      library by this mode.

  --emit-tests DIR
      Write exhaustive-equivalence regression tests (model == CBMC's native
      vector operator for all inputs) under DIR for every model with an
      oracle. Used to (re)generate the per-function cbmc-library tests.

Typical workflow for adding intrinsics
--------------------------------------
  1. scripts/generate_intrinsic_models.py --status --xml data-latest.xml
     to find declared-but-unmodeled builtins with tractable pseudocode;
  2. --emit-drafts data-latest.xml to get draft Model() entries;
  3. review/finish each draft (signedness, UB-hardening) and add it to MODELS;
  4. -o src/ansi-c/library/x86_intrinsics.c to regenerate the library;
  5. --emit-tests regression/cbmc-library/__builtin_ia32 to refresh tests.

The Intel Intrinsics Guide XML used by --xml/--emit-drafts can be downloaded
from:
  https://www.intel.com/content/dam/develop/public/us/en/include/intrinsics-guide/data-latest.xml
"""

import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET
from dataclasses import dataclass

# GCC vector types used in CBMC headers, keyed by (element_c_type, count)
VEC_TYPES = {
    ("char", 16):      "__gcc_v16qi",
    ("short", 8):      "__gcc_v8hi",
    ("int", 4):        "__gcc_v4si",
    ("long long", 2):  "__gcc_v2di",
    ("float", 4):      "__gcc_v4sf",
    ("double", 2):     "__gcc_v2df",
    ("char", 8):       "__gcc_v8qi",
    ("short", 4):      "__gcc_v4hi",
    ("int", 2):        "__gcc_v2si",
    # 256-bit (AVX2)
    ("char", 32):      "__gcc_v32qi",
    ("short", 16):     "__gcc_v16hi",
    ("int", 8):        "__gcc_v8si",
    ("long long", 4):  "__gcc_v4di",
    # 512-bit (AVX-512)
    ("char", 64):      "__gcc_v64qi",
    ("short", 32):     "__gcc_v32hi",
    ("int", 16):       "__gcc_v16si",
    ("long long", 8):  "__gcc_v8di",
}

# AVX-512 write-mask C type (__mmask8/16/32/64) for a given lane count: the
# smallest mask type with at least one bit per lane.
def mask_type_for(count):
    if count <= 8:
        return "unsigned char"
    if count <= 16:
        return "unsigned short"
    if count <= 32:
        return "unsigned int"
    if count <= 64:
        return "unsigned long long"
    return None

# Bytes per element C type.
ELEM_SIZE = {"char": 1, "short": 2, "int": 4, "long long": 8}

# The library file this tool owns and (re)generates. Its models are this
# tool's own output, so they are excluded from the "already modeled elsewhere"
# check that decides what to emit (keeping regeneration idempotent).
GENERATED_LIBRARY = os.path.join("src", "ansi-c", "library", "x86_intrinsics.c")


@dataclass
class Model:
    """A single per-element SIMD intrinsic model.

    builtin: the GCC __builtin_ia32_* name the model implements.
    elem:    base element C type ("char", "short", "int", "long long").
    count:   number of lanes.
    body:    per-element body template using {a}, {b} (operands) and {j}
             (lane index), assigned to dst[j].
    sign:    how the per-element operation is carried out, by aliasing the
             operands to a vector of the chosen signedness before the loop and
             casting the result back:
               ""         - use the (signed-by-default) vector type as-is;
               "signed"   - force signed semantics. Needed where 'char' may be
                            unsigned (e.g. ARM): without this '< 0' is always
                            false (-Werror=type-limits in library_check.sh) and
                            'a > b' would silently become an unsigned compare,
                            which is wrong for signed intrinsics like
                            _mm_max_epi8;
               "unsigned" - perform the operation in the matching unsigned type.
                            Used both for genuinely unsigned intrinsics (min/max
                            epu*, avg) and for the wrapping signed-arithmetic
                            intrinsics (add/sub/mullo on 32/64-bit lanes), where
                            'int + int' etc. would be signed-overflow UB:
                            unsigned arithmetic is well-defined modular and the
                            cast back reproduces the two's-complement result.
    scalar2: C type of a scalar second parameter (e.g. "int" for a shift
             count) instead of a second vector operand. When set, the body
             refers to it as {b} (a scalar, not {b}[{j}]).
    oracle:  a native C vector operator ("+", "-", "*") for which CBMC's own
             vector semantics provide an independent reference; --emit-tests
             then generates an exhaustive equivalence proof (model == native
             operator for all inputs).
    mask_type: when set (to an __mmask C type), this is an AVX-512 merge-masked
             variant: the function takes (a, b, merge-source, mask) and each
             lane is the base body if its mask bit is set, else the merge
             source. body/sign describe the underlying (unmasked) operation.
    """
    builtin: str
    elem: str
    count: int
    body: str
    sign: str = ""
    scalar2: str = None
    oracle: str = None
    mask_type: str = None


# Intel _mm_* name -> Model
MODELS = {
    # --- add (32/64-bit done unsigned to avoid signed-overflow UB) ---
    "_mm_add_epi8":  Model("__builtin_ia32_paddb128", "char", 16, "{a}[{j}] + {b}[{j}]", oracle="+"),
    "_mm_add_epi16": Model("__builtin_ia32_paddw128", "short", 8, "{a}[{j}] + {b}[{j}]", oracle="+"),
    "_mm_add_epi32": Model("__builtin_ia32_paddd128", "int", 4, "{a}[{j}] + {b}[{j}]", sign="unsigned", oracle="+"),
    "_mm_add_epi64": Model("__builtin_ia32_paddq128", "long long", 2, "{a}[{j}] + {b}[{j}]", sign="unsigned", oracle="+"),
    # --- sub (ditto) ---
    "_mm_sub_epi8":  Model("__builtin_ia32_psubb128", "char", 16, "{a}[{j}] - {b}[{j}]", oracle="-"),
    "_mm_sub_epi16": Model("__builtin_ia32_psubw128", "short", 8, "{a}[{j}] - {b}[{j}]", oracle="-"),
    "_mm_sub_epi32": Model("__builtin_ia32_psubd128", "int", 4, "{a}[{j}] - {b}[{j}]", sign="unsigned", oracle="-"),
    "_mm_sub_epi64": Model("__builtin_ia32_psubq128", "long long", 2, "{a}[{j}] - {b}[{j}]", sign="unsigned", oracle="-"),
    # --- min/max signed ---
    "_mm_min_epi8":  Model("__builtin_ia32_pminsb128", "char", 16, "{a}[{j}] < {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="signed"),
    "_mm_min_epi16": Model("__builtin_ia32_pminsw128", "short", 8, "{a}[{j}] < {b}[{j}] ? {a}[{j}] : {b}[{j}]"),
    "_mm_min_epi32": Model("__builtin_ia32_pminsd128", "int", 4, "{a}[{j}] < {b}[{j}] ? {a}[{j}] : {b}[{j}]"),
    "_mm_max_epi8":  Model("__builtin_ia32_pmaxsb128", "char", 16, "{a}[{j}] > {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="signed"),
    "_mm_max_epi16": Model("__builtin_ia32_pmaxsw128", "short", 8, "{a}[{j}] > {b}[{j}] ? {a}[{j}] : {b}[{j}]"),
    "_mm_max_epi32": Model("__builtin_ia32_pmaxsd128", "int", 4, "{a}[{j}] > {b}[{j}] ? {a}[{j}] : {b}[{j}]"),
    # --- min/max unsigned ---
    "_mm_min_epu8":  Model("__builtin_ia32_pminub128", "char", 16, "{a}[{j}] < {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="unsigned"),
    "_mm_max_epu8":  Model("__builtin_ia32_pmaxub128", "char", 16, "{a}[{j}] > {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="unsigned"),
    "_mm_min_epu16": Model("__builtin_ia32_pminuw128", "short", 8, "{a}[{j}] < {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="unsigned"),
    "_mm_max_epu16": Model("__builtin_ia32_pmaxuw128", "short", 8, "{a}[{j}] > {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="unsigned"),
    "_mm_min_epu32": Model("__builtin_ia32_pminud128", "int", 4, "{a}[{j}] < {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="unsigned"),
    "_mm_max_epu32": Model("__builtin_ia32_pmaxud128", "int", 4, "{a}[{j}] > {b}[{j}] ? {a}[{j}] : {b}[{j}]", sign="unsigned"),
    # --- abs (32-bit uses unsigned modular negation to avoid -INT_MIN UB) ---
    "_mm_abs_epi8":  Model("__builtin_ia32_pabsb128", "char", 16, "{a}[{j}] < 0 ? -{a}[{j}] : {a}[{j}]", sign="signed"),
    "_mm_abs_epi16": Model("__builtin_ia32_pabsw128", "short", 8, "{a}[{j}] < 0 ? -{a}[{j}] : {a}[{j}]"),
    "_mm_abs_epi32": Model("__builtin_ia32_pabsd128", "int", 4, "{a}[{j}] < 0 ? (int)(0u - (unsigned){a}[{j}]) : {a}[{j}]"),
    # --- compare (result is all-1s or all-0s per element) ---
    "_mm_cmpeq_epi8":  Model("__builtin_ia32_pcmpeqb128", "char", 16, "{a}[{j}] == {b}[{j}] ? -1 : 0", oracle="=="),
    "_mm_cmpeq_epi16": Model("__builtin_ia32_pcmpeqw128", "short", 8, "{a}[{j}] == {b}[{j}] ? -1 : 0", oracle="=="),
    "_mm_cmpeq_epi32": Model("__builtin_ia32_pcmpeqd128", "int", 4, "{a}[{j}] == {b}[{j}] ? -1 : 0", oracle="=="),
    "_mm_cmpgt_epi8":  Model("__builtin_ia32_pcmpgtb128", "char", 16, "{a}[{j}] > {b}[{j}] ? -1 : 0", sign="signed", oracle=">"),
    "_mm_cmpgt_epi16": Model("__builtin_ia32_pcmpgtw128", "short", 8, "{a}[{j}] > {b}[{j}] ? -1 : 0", oracle=">"),
    "_mm_cmpgt_epi32": Model("__builtin_ia32_pcmpgtd128", "int", 4, "{a}[{j}] > {b}[{j}] ? -1 : 0", oracle=">"),
    # --- average unsigned ---
    "_mm_avg_epu8":  Model("__builtin_ia32_pavgb128", "char", 16, "({a}[{j}] + {b}[{j}] + 1) >> 1", sign="unsigned"),
    "_mm_avg_epu16": Model("__builtin_ia32_pavgw128", "short", 8, "({a}[{j}] + {b}[{j}] + 1) >> 1", sign="unsigned"),
    # --- mullo (low half of multiply; 32-bit done unsigned to avoid UB) ---
    "_mm_mullo_epi16": Model("__builtin_ia32_pmullw128", "short", 8, "{a}[{j}] * {b}[{j}]"),
    "_mm_mullo_epi32": Model("__builtin_ia32_pmulld128", "int", 4, "{a}[{j}] * {b}[{j}]", sign="unsigned"),
    # --- bitwise (whole-register; modelled on 64-bit lanes) ---
    "_mm_and_si128":    Model("__builtin_ia32_pand128", "long long", 2, "{a}[{j}] & {b}[{j}]", oracle="&"),
    "_mm_or_si128":     Model("__builtin_ia32_por128", "long long", 2, "{a}[{j}] | {b}[{j}]", oracle="|"),
    "_mm_xor_si128":    Model("__builtin_ia32_pxor128", "long long", 2, "{a}[{j}] ^ {b}[{j}]", oracle="^"),
    "_mm_andnot_si128": Model("__builtin_ia32_pandn128", "long long", 2, "~{a}[{j}] & {b}[{j}]", oracle="andnot"),
    # --- MMX 64-bit add/sub (32-bit lanes done unsigned to avoid UB) ---
    "_mm_add_pi8":  Model("__builtin_ia32_paddb", "char", 8, "{a}[{j}] + {b}[{j}]", oracle="+"),
    "_mm_add_pi16": Model("__builtin_ia32_paddw", "short", 4, "{a}[{j}] + {b}[{j}]", oracle="+"),
    "_mm_add_pi32": Model("__builtin_ia32_paddd", "int", 2, "{a}[{j}] + {b}[{j}]", sign="unsigned", oracle="+"),
    "_mm_sub_pi8":  Model("__builtin_ia32_psubb", "char", 8, "{a}[{j}] - {b}[{j}]", oracle="-"),
    "_mm_sub_pi16": Model("__builtin_ia32_psubw", "short", 4, "{a}[{j}] - {b}[{j}]", oracle="-"),
    "_mm_sub_pi32": Model("__builtin_ia32_psubd", "int", 2, "{a}[{j}] - {b}[{j}]", sign="unsigned", oracle="-"),
    # --- saturating add: clamp to the element type's range ---
    "_mm_adds_epi8":  Model("__builtin_ia32_paddsb128", "char", 16, "({a}[{j}] + {b}[{j}]) < -128 ? -128 : ({a}[{j}] + {b}[{j}]) > 127 ? 127 : {a}[{j}] + {b}[{j}]", sign="signed"),
    "_mm_adds_epi16": Model("__builtin_ia32_paddsw128", "short", 8, "({a}[{j}] + {b}[{j}]) < -32768 ? -32768 : ({a}[{j}] + {b}[{j}]) > 32767 ? 32767 : {a}[{j}] + {b}[{j}]"),
    "_mm_adds_epu8":  Model("__builtin_ia32_paddusb128", "char", 16, "({a}[{j}] + {b}[{j}]) > 255 ? 255 : {a}[{j}] + {b}[{j}]", sign="unsigned"),
    "_mm_adds_epu16": Model("__builtin_ia32_paddusw128", "short", 8, "({a}[{j}] + {b}[{j}]) > 65535 ? 65535 : {a}[{j}] + {b}[{j}]", sign="unsigned"),
    # --- saturating sub ---
    "_mm_subs_epi8":  Model("__builtin_ia32_psubsb128", "char", 16, "({a}[{j}] - {b}[{j}]) < -128 ? -128 : ({a}[{j}] - {b}[{j}]) > 127 ? 127 : {a}[{j}] - {b}[{j}]", sign="signed"),
    "_mm_subs_epi16": Model("__builtin_ia32_psubsw128", "short", 8, "({a}[{j}] - {b}[{j}]) < -32768 ? -32768 : ({a}[{j}] - {b}[{j}]) > 32767 ? 32767 : {a}[{j}] - {b}[{j}]"),
    "_mm_subs_epu8":  Model("__builtin_ia32_psubusb128", "char", 16, "({a}[{j}] - {b}[{j}]) < 0 ? 0 : {a}[{j}] - {b}[{j}]", sign="unsigned"),
    "_mm_subs_epu16": Model("__builtin_ia32_psubusw128", "short", 8, "({a}[{j}] - {b}[{j}]) < 0 ? 0 : {a}[{j}] - {b}[{j}]", sign="unsigned"),
    # --- shift by immediate (count in a scalar int) ---
    # Logical shifts use unsigned lanes (well-defined modular shift); a count
    # of >= element width yields 0. Casting the count to unsigned also makes a
    # negative/out-of-range immediate clamp to "too large" rather than UB.
    "_mm_slli_epi16": Model("__builtin_ia32_psllwi128", "short", 8, "(unsigned){b} >= 16 ? 0 : {a}[{j}] << {b}", sign="unsigned", scalar2="int"),
    "_mm_slli_epi32": Model("__builtin_ia32_pslldi128", "int", 4, "(unsigned){b} >= 32 ? 0 : {a}[{j}] << {b}", sign="unsigned", scalar2="int"),
    "_mm_slli_epi64": Model("__builtin_ia32_psllqi128", "long long", 2, "(unsigned){b} >= 64 ? 0 : {a}[{j}] << {b}", sign="unsigned", scalar2="int"),
    "_mm_srli_epi16": Model("__builtin_ia32_psrlwi128", "short", 8, "(unsigned){b} >= 16 ? 0 : {a}[{j}] >> {b}", sign="unsigned", scalar2="int"),
    "_mm_srli_epi32": Model("__builtin_ia32_psrldi128", "int", 4, "(unsigned){b} >= 32 ? 0 : {a}[{j}] >> {b}", sign="unsigned", scalar2="int"),
    "_mm_srli_epi64": Model("__builtin_ia32_psrlqi128", "long long", 2, "(unsigned){b} >= 64 ? 0 : {a}[{j}] >> {b}", sign="unsigned", scalar2="int"),
    # Arithmetic right shift uses signed lanes; a count of >= width yields the
    # sign fill (-1 for negative inputs, 0 otherwise).
    "_mm_srai_epi16": Model("__builtin_ia32_psrawi128", "short", 8, "(unsigned){b} >= 16 ? ({a}[{j}] < 0 ? -1 : 0) : {a}[{j}] >> {b}", scalar2="int"),
    "_mm_srai_epi32": Model("__builtin_ia32_psradi128", "int", 4, "(unsigned){b} >= 32 ? ({a}[{j}] < 0 ? -1 : 0) : {a}[{j}] >> {b}", scalar2="int"),
}


def width_variants(declared):
    """Derive wider-vector variants of the 128-bit base MODELS entries.

    The per-element body is width-independent, so a 256-bit (AVX2) variant
    differs only in the builtin name (...128 -> ...256), the Intel name
    (_mm_ -> _mm256_) and the lane count (doubled). A variant is produced only
    when its builtin is actually declared in CBMC's headers. (512-bit AVX-512
    forms are mask-only -- e.g. ...512_mask -- and are handled separately.)"""
    variants = {}
    for intel_name, m in MODELS.items():
        if not m.builtin.endswith("128"):
            continue
        builtin256 = m.builtin[:-len("128")] + "256"
        if builtin256 not in declared:
            continue
        name256 = intel_name.replace("_mm_", "_mm256_", 1)
        variants[name256] = Model(
            builtin256, m.elem, m.count * 2, m.body, m.sign, m.scalar2,
            m.oracle)
    return variants


def mask_variants(declared):
    """Derive AVX-512 merge-masked variants (128-, 256- and 512-bit) of the
    binary pointwise base entries (those with a second vector operand and no
    scalar parameter), gated on the ...<width>_mask builtin being declared.
    The masking is a uniform wrapper over the base per-element body. (There is
    no separate _maskz builtin for these ops: zero-masking is the _mask form
    with a zero merge source.)"""
    variants = {}
    for intel_name, m in MODELS.items():
        if m.scalar2 or "{b}" not in m.body or not m.builtin.endswith("128"):
            continue
        # Masked compares (pcmp*_mask) are not merge-masked vector ops: they
        # return an __mmask and take (a, b, k), so the merge-mask wrapper below
        # would give them the wrong signature. Skip the compare base ops.
        if m.oracle in ("==", ">"):
            continue
        mnemonic = m.builtin[len("__builtin_ia32_"):-len("128")]
        for width, factor in (("128", 1), ("256", 2), ("512", 4)):
            builtin = f"__builtin_ia32_{mnemonic}{width}_mask"
            count = m.count * factor
            mask_type = mask_type_for(count)
            if (builtin not in declared or mask_type is None
                    or (m.elem, count) not in VEC_TYPES):
                continue
            prefix = "_mm_mask_" if width == "128" else f"_mm{width}_mask_"
            name = intel_name.replace("_mm_", prefix, 1)
            variants[name] = Model(
                builtin, m.elem, count, m.body, m.sign, mask_type=mask_type)
    return variants


def get_existing_models(cbmc_root, exclude=None):
    """Collect __builtin_ia32_* models already present in the library. When
    regenerating a file, that file is passed as *exclude* so its own models do
    not count as "already present" (keeping regeneration idempotent)."""
    models = set()
    lib_dir = os.path.join(cbmc_root, "src", "ansi-c", "library")
    exclude = os.path.abspath(exclude) if exclude else None
    for fname in os.listdir(lib_dir):
        if not fname.endswith(".c"):
            continue
        path = os.path.join(lib_dir, fname)
        if exclude and os.path.abspath(path) == exclude:
            continue
        with open(path) as f:
            for m in re.finditer(r'/\* FUNCTION: (__builtin_ia32_\w+)', f.read()):
                models.add(m.group(1))
    return models


def get_declared_builtins(cbmc_root):
    builtins = set()
    pattern = os.path.join(cbmc_root, "src", "ansi-c", "compiler_headers",
                           "gcc_builtin_headers_ia32*.h")
    for hdr in glob.glob(pattern):
        with open(hdr) as f:
            for m in re.finditer(r'(__builtin_ia32_\w+)', f.read()):
                builtins.add(m.group(1))
    return builtins


def emit_model(model):
    """Emit a CBMC library model function for a Model, or None if the
    (element type, count) combination has no known GCC vector type."""
    vec_type = VEC_TYPES.get((model.elem, model.count))
    if vec_type is None:
        return None

    total_bytes = model.count * ELEM_SIZE[model.elem]
    vec_typedef = (f"typedef {model.elem} {vec_type} "
                   f"__attribute__((__vector_size__({total_bytes})));")

    lines = [f"/* FUNCTION: {model.builtin} */", "", vec_typedef, ""]

    # Determine the type the per-element operation runs in (work_type) and,
    # if it differs from the public vector type, the alias typedef for it.
    work_type = vec_type
    if model.sign in ("signed", "unsigned"):
        work_type = f"{vec_type}_{'u' if model.sign == 'unsigned' else 's'}"
        work_typedef = (f"typedef {model.sign} {model.elem} {work_type} "
                        f"__attribute__((__vector_size__({total_bytes})));")
        lines.insert(3, work_typedef)

    scalar = model.scalar2 is not None
    n_params = 2 if (scalar or "{b}" in model.body) else 1
    # A scalar second operand is referred to directly as {b} (not {b}[{j}]).
    body = model.body.format(a="a_", b=("b" if scalar else "b_"), j="j")
    cast = f"({work_type})" if work_type != vec_type else ""

    if n_params == 1:
        lines.append(f"{vec_type} {model.builtin}({vec_type} a)")
    elif scalar:
        lines.append(
            f"{vec_type} {model.builtin}({vec_type} a, {model.scalar2} b)")
    else:
        lines.append(f"{vec_type} {model.builtin}({vec_type} a, {vec_type} b)")

    lines.append("{")
    lines.append(f"  {work_type} a_ = {cast}a;")
    if n_params > 1 and not scalar:
        lines.append(f"  {work_type} b_ = {cast}b;")
    lines.append(f"  {work_type} dst;")
    lines.append(f"  for(int j = 0; j < {model.count}; j++)")
    lines.append(f"    dst[j] = {body};")
    if work_type != vec_type:
        lines.append(f"  return ({vec_type})dst;")
    else:
        lines.append("  return dst;")
    lines.append("}")
    lines.append("")
    return "\n".join(lines)


def emit_masked_model(model):
    """Emit an AVX-512 merge-masked model: per lane, the base body if the
    mask bit is set, otherwise the corresponding lane of the merge source."""
    vec_type = VEC_TYPES.get((model.elem, model.count))
    if vec_type is None:
        return None
    total_bytes = model.count * ELEM_SIZE[model.elem]
    lines = [f"/* FUNCTION: {model.builtin} */", "",
             f"typedef {model.elem} {vec_type} "
             f"__attribute__((__vector_size__({total_bytes})));"]
    work_type = vec_type
    if model.sign in ("signed", "unsigned"):
        work_type = f"{vec_type}_{'u' if model.sign == 'unsigned' else 's'}"
        lines.append(f"typedef {model.sign} {model.elem} {work_type} "
                     f"__attribute__((__vector_size__({total_bytes})));")
    lines.append("")
    body = model.body.format(a="a_", b="b_", j="j")
    cast = f"({work_type})" if work_type != vec_type else ""
    lines.append(f"{vec_type} {model.builtin}({vec_type} a, {vec_type} b, "
                 f"{vec_type} src, {model.mask_type} k)")
    lines.append("{")
    lines.append(f"  {work_type} a_ = {cast}a;")
    lines.append(f"  {work_type} b_ = {cast}b;")
    lines.append(f"  {vec_type} dst;")
    lines.append(f"  for(int j = 0; j < {model.count}; j++)")
    lines.append(f"    dst[j] = (k >> j) & 1 ? ({model.elem})({body}) : src[j];")
    lines.append("  return dst;")
    lines.append("}")
    lines.append("")
    return "\n".join(lines)


# --- Intel Intrinsics Guide XML survey (--xml) -----------------------------

# Base C element type for an element bit width.
_BITS_TO_ELEM = {8: "char", 16: "short", 32: "int", 64: "long long"}


def parse_operation(op_text):
    """Translate a simple element-wise Intel <operation> into
    (elem, count, body) for the generator, or None if it is not the supported
    shape: a single 'FOR j := 0 to N' loop with one
    'dst[i+W-1:i] := <expr>' assignment whose expression uses only the per-lane
    operands a/b, the operators + - *, and parentheses.

    This deliberately does NOT infer signedness or apply the UB-hardening
    (unsigned wrapping arithmetic etc.) that the hand-written MODELS use, so
    its output is a draft for human review rather than a finished model."""
    if not op_text:
        return None
    # Drop trailing upper-bits-zero lines such as 'dst[MAX:256] := 0'.
    lines = [ln for ln in op_text.strip().splitlines()
             if not re.match(r'\s*dst\[(?:MAX|\d+):\d+\]\s*:=\s*0\s*$', ln)]
    text = "\n".join(lines)
    m_for = re.search(r'FOR\s+j\s*:=\s*0\s+to\s+(\d+)', text)
    if not m_for or len(re.findall(r'\bFOR\b', text)) != 1:
        return None
    count = int(m_for.group(1)) + 1
    assignments = re.findall(r'dst\[i\+(\d+):i\]\s*:=\s*(.+)', text)
    if len(assignments) != 1:
        return None
    width = int(assignments[0][0]) + 1
    elem = _BITS_TO_ELEM.get(width)
    if elem is None:
        return None
    expr = assignments[0][1].strip()
    # Reject widening/narrowing ops: every operand lane slice must have the
    # same width as the destination lane (e.g. _mm_mul_epu32 reads 32-bit
    # halves into a 64-bit dst and must not be translated element-wise).
    operand_widths = {int(w) + 1
                      for w in re.findall(r'\b[ab]\[i\+(\d+):i\]', expr)}
    if operand_widths and operand_widths != {width}:
        return None
    # Per-lane slices a[i+W-1:i] / b[i+W-1:i] become {a}[{j}] / {b}[{j}].
    expr = re.sub(r'\ba\[i\+\d+:i\]', '{a}[{j}]', expr)
    expr = re.sub(r'\bb\[i\+\d+:i\]', '{b}[{j}]', expr)
    # Anything other than the lane placeholders, + - *, parentheses and
    # whitespace means we do not fully understand the expression.
    residue = re.sub(r'\{a\}\[\{j\}\]|\{b\}\[\{j\}\]|[-+*()\s]', '', expr)
    if residue:
        return None
    return elem, count, expr


def xml_emit_drafts(xml_path, declared, existing, all_models):
    """Return (drafts, geometry_mismatches). drafts maps a not-yet-modeled
    declared builtin to (intel_name, elem, count, body) derived from its
    pseudocode. geometry_mismatches lists already-modeled builtins where the
    translator's (elem, count) disagrees with the hand-written Model -- a
    self-check that the translator reads the pseudocode geometry correctly."""
    root = ET.parse(xml_path).getroot()
    builtin_to_model = {m.builtin: m for m in all_models.values()}
    modeled = set(builtin_to_model) | existing
    drafts = {}
    mismatches = []
    for intrinsic in root.iter("intrinsic"):
        operation = intrinsic.find("operation")
        parsed = parse_operation(
            operation.text if operation is not None else None)
        if not parsed:
            continue
        elem, count, body = parsed
        for builtin in _builtin_candidates(intrinsic):
            if builtin not in declared:
                continue
            model = builtin_to_model.get(builtin)
            if model is not None:
                if (model.elem, model.count) != (elem, count):
                    mismatches.append(
                        (builtin, (elem, count), (model.elem, model.count)))
            elif builtin not in modeled:
                drafts.setdefault(
                    builtin, (intrinsic.get("name"), elem, count, body))
    return drafts, mismatches


# Width (and hence GCC builtin suffix) implied by an <instruction> form.
def _instruction_width(form):
    f = (form or "").lower()
    if "zmm" in f:
        return "512"
    if "ymm" in f:
        return "256"
    if "xmm" in f:
        return "128"
    if "mm" in f:
        return ""  # 64-bit MMX builtins typically carry no width suffix
    return None


def _builtin_candidates(intrinsic):
    """Best-effort set of GCC builtin names an <intrinsic> might correspond to,
    derived from its <instruction> mnemonic(s) and register width. Heuristic:
    AVX-512 masked variants and a few irregular names will not map."""
    out = set()
    for instr in intrinsic.findall("instruction"):
        mnemonic = (instr.get("name") or "").lower()
        width = _instruction_width(instr.get("form"))
        if mnemonic and width is not None:
            out.add(f"__builtin_ia32_{mnemonic}{width}")
    return out


def _is_auto_generatable(operation):
    """Heuristic: does this <operation> pseudocode have the simple per-element
    shape the generator can already emit (a single FOR loop assigning dst[...]
    from a/b, with no control flow or helper-function calls)?"""
    if not operation:
        return False
    s = operation.strip()
    # exactly one FOR ... ENDFOR (note "ENDFOR" also contains "FOR")
    if len(re.findall(r'\bFOR\b', s)) != 1 or "ENDFOR" not in s:
        return False
    if re.search(r'\b(CASE|IF|ELSE|RETURN|DEFINE|WHILE)\b', s):
        return False
    body = "\n".join(line for line in s.splitlines()
                     if not re.search(r'\b(FOR|ENDFOR)\b', line))
    if "dst[" not in body:
        return False
    # reject helper-function calls such as ABS(), SignExtend(), Saturate*()
    if re.search(r'[A-Za-z_]\w*\s*\(', body):
        return False
    return True


def xml_autogen_candidates(xml_path, declared, existing):
    """Return a sorted list of (intel_name, builtin) for not-yet-modeled
    builtins whose Intel pseudocode looks auto-generatable, plus the total
    number of auto-generatable intrinsics seen (regardless of mapping)."""
    root = ET.parse(xml_path).getroot()
    missing = declared - existing
    candidates = {}
    total_parseable = 0
    for intrinsic in root.iter("intrinsic"):
        operation = intrinsic.find("operation")
        op_text = operation.text if operation is not None else None
        if not _is_auto_generatable(op_text):
            continue
        total_parseable += 1
        name = intrinsic.get("name")
        for builtin in _builtin_candidates(intrinsic):
            if builtin in missing:
                candidates.setdefault(builtin, name)
    return (sorted((name, b) for b, name in candidates.items()),
            total_parseable)


def xml_cpuid_coverage(xml_path, declared, existing):
    """Per CPUID feature, how many mappable-to-declared builtins are modeled.
    Returns rows (feature, modeled_count, declared_count) sorted by declared
    count descending. Grouped by the intrinsic's first <CPUID> element."""
    from collections import defaultdict
    root = ET.parse(xml_path).getroot()
    decl = defaultdict(set)
    modeled = defaultdict(set)
    for intrinsic in root.iter("intrinsic"):
        feature = intrinsic.findtext("CPUID") or "(none)"
        for builtin in _builtin_candidates(intrinsic):
            if builtin in declared:
                decl[feature].add(builtin)
                if builtin in existing:
                    modeled[feature].add(builtin)
    return [(feat, len(modeled[feat]), len(decl[feat]))
            for feat in sorted(decl, key=lambda f: len(decl[f]), reverse=True)]


def format_output(text, assume_filename):
    """Run generated C through clang-format so bodies of any length come out
    matching the project style (and the CI clang-format check). A no-op on
    already-clean output; if clang-format is unavailable the text is returned
    unchanged (CI's clang-format check would then catch any divergence).
    *assume_filename* tells clang-format which .clang-format / language to use."""
    for clang_format in ("clang-format-15", "clang-format"):
        if shutil.which(clang_format):
            result = subprocess.run(
                [clang_format, "--assume-filename", assume_filename],
                input=text, capture_output=True, text=True)
            if result.returncode == 0:
                return result.stdout
            break
    sys.stderr.write("warning: clang-format not found; output not reformatted\n")
    return text


def equivalence_test(model):
    """C source for an exhaustive equivalence test: model(a, b) must equal a
    reference built from CBMC's native vector operators for all inputs. The
    reference is independent of the library model (CBMC implements vector
    operators directly). Returns None if the model has no oracle / no vector
    type.

    Arithmetic references (+, -, *) are computed on unsigned lanes so they are
    overflow-clean and wrap like the hardware; bitwise and comparison
    references use the signed vector type directly (signedness is irrelevant
    to & | ^ and ==, and pcmpgt is a signed compare)."""
    if not model.oracle:
        return None
    vec = VEC_TYPES.get((model.elem, model.count))
    if vec is None:
        return None
    nbytes = model.count * ELEM_SIZE[model.elem]
    decls = [f"typedef {model.elem} {vec} "
             f"__attribute__((__vector_size__({nbytes})));"]
    if model.oracle in ("+", "-", "*"):
        uvec = vec + "_u"
        decls.append(f"typedef unsigned {model.elem} {uvec} "
                     f"__attribute__((__vector_size__({nbytes})));")
        ref_type = uvec
        ref_expr = f"({uvec})a {model.oracle} ({uvec})b"
        lane = lambda k: f"r[{k}] == ({model.elem})ref[{k}]"
        desc = f"native {model.oracle}"
    elif model.oracle == "andnot":
        ref_type = vec
        ref_expr = "~a & b"
        lane = lambda k: f"r[{k}] == ref[{k}]"
        desc = "native ~a & b"
    else:  # & | ^ == >
        ref_type = vec
        ref_expr = f"a {model.oracle} b"
        lane = lambda k: f"r[{k}] == ref[{k}]"
        desc = f"native {model.oracle}"
    decls.append(f"{vec} {model.builtin}({vec}, {vec});")
    lanes = " && ".join(lane(k) for k in range(model.count))
    return (
        "\n".join(decls) + "\n\n"
        "int main()\n"
        "{\n"
        "  // Exhaustive equivalence: the model must agree with CBMC's own\n"
        f"  // vector semantics ({desc}) for all inputs.\n"
        f"  {vec} a, b;\n"
        f"  {vec} r = {model.builtin}(a, b);\n"
        f"  {ref_type} ref = {ref_expr};\n"
        f"  __CPROVER_assert(\n    {lanes},\n"
        f'    "{model.builtin} == {desc}");\n'
        "  return 0;\n"
        "}\n")


TEST_DESC = ("CORE gcc-only\nmain.c\n\n"
             "^EXIT=0$\n^SIGNAL=0$\n^VERIFICATION SUCCESSFUL$\n--\n"
             "^warning: ignoring\n")


def emit_tests(out_dir, all_models):
    """Write an exhaustive-equivalence regression test (main.c + test.desc)
    under out_dir/<builtin>/ for every model that has a native-operator
    oracle. Returns the number of tests written."""
    written = 0
    for model in all_models.values():
        source = equivalence_test(model)
        if source is None:
            continue
        test_dir = os.path.join(out_dir, model.builtin)
        os.makedirs(test_dir, exist_ok=True)
        main_c = os.path.join(test_dir, "main.c")
        with open(main_c, "w") as f:
            f.write(format_output(source, main_c))
        with open(os.path.join(test_dir, "test.desc"), "w") as f:
            f.write(TEST_DESC)
        written += 1
    return written


def main():
    p = argparse.ArgumentParser(description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--cbmc-root", default=".")
    p.add_argument("-o", "--output")
    p.add_argument("--status", action="store_true",
                   help="Show declared vs modeled intrinsics")
    p.add_argument("--xml",
                   help="Intel Intrinsics Guide data-latest.xml; with --status, "
                        "survey which not-yet-modeled builtins have "
                        "auto-generatable pseudocode")
    p.add_argument("--emit-drafts", metavar="XML",
                   help="Translate the simple element-wise pseudocode of "
                        "not-yet-modeled intrinsics into draft Model() entries "
                        "for review (signedness and UB-hardening still need a "
                        "human), and self-check the translator against the "
                        "hand-written models")
    p.add_argument("--emit-tests", metavar="DIR",
                   help="Write exhaustive-equivalence regression tests "
                        "(model == CBMC's native vector operator for all "
                        "inputs) under DIR for every model with an oracle")
    args = p.parse_args()

    existing = get_existing_models(args.cbmc_root)
    declared = get_declared_builtins(args.cbmc_root)
    # The base 128-bit MODELS plus derived wider-vector variants (gated on the
    # builtin being declared) form the full set this tool can emit.
    all_models = {**MODELS, **width_variants(declared),
                  **mask_variants(declared)}

    if args.emit_tests:
        n = emit_tests(args.emit_tests, all_models)
        sys.stderr.write(f"Wrote {n} equivalence test(s) under "
                         f"{args.emit_tests}\n")
        return

    if args.emit_drafts:
        drafts, mismatches = xml_emit_drafts(
            args.emit_drafts, declared, existing, all_models)
        sys.stderr.write(
            f"Translator self-check: {len(mismatches)} geometry mismatch(es) "
            f"against hand-written models.\n")
        for builtin, got, want in mismatches:
            sys.stderr.write(f"  MISMATCH {builtin}: derived {got} vs {want}\n")
        print(f"# {len(drafts)} draft model(s) from element-wise pseudocode.")
        print("# Review each: infer signedness, and harden against signed UB")
        print("# (unsigned wrapping arithmetic, modular negation) before use.")
        for builtin in sorted(drafts):
            iname, elem, count, body = drafts[builtin]
            print(f'    "{iname}": Model("{builtin}", "{elem}", {count}, '
                  f'"{body}"),')
        return

    if args.status:
        print(f"Declared __builtin_ia32_* in CBMC headers: {len(declared)}")
        print(f"Already modeled in library: {len(existing)}")
        print(f"Missing models: {len(declared) - len(existing)}")
        can = [(iname, m.builtin) for iname, m in all_models.items()
               if m.builtin in declared and m.builtin not in existing]
        print(f"\nCan auto-generate from MODELS ({len(can)}):")
        for iname, bname in sorted(can, key=lambda x: x[1]):
            print(f"  {bname}  ({iname})")
        not_yet = declared - existing - {m.builtin for m in all_models.values()}
        print(f"\nNot yet covered by this tool: {len(not_yet)}")
        if args.xml:
            candidates, total = xml_autogen_candidates(
                args.xml, declared, existing)
            print(f"\nIntel intrinsics with auto-generatable pseudocode: "
                  f"{total}")
            print(f"... mapping to a not-yet-modeled CBMC builtin "
                  f"({len(candidates)}):")
            for iname, bname in candidates:
                print(f"  {bname}  ({iname})")
            rows = xml_cpuid_coverage(args.xml, declared, existing)
            print(f"\nCoverage by CPUID feature (modeled / mappable-declared):")
            for feat, n_modeled, n_declared in rows:
                print(f"  {feat:20s} {n_modeled:5d} / {n_declared}")
        return

    # Emit a model unless that builtin is already modeled in another library
    # file (the owned GENERATED_LIBRARY is excluded so regeneration is
    # idempotent rather than emitting nothing).
    external = get_existing_models(
        args.cbmc_root, exclude=os.path.join(args.cbmc_root, GENERATED_LIBRARY))
    models = []
    for intel_name, model in sorted(all_models.items(),
                                    key=lambda x: x[1].builtin):
        if model.builtin in external:
            continue
        if model.builtin not in declared:
            print(f"Skip {model.builtin}: not declared in CBMC headers",
                  file=sys.stderr)
            continue
        emitted = (emit_masked_model(model) if model.mask_type
                   else emit_model(model))
        if emitted:
            models.append(emitted)

    header = (
        "// x86 SIMD intrinsic models for CBMC\n"
        "// Generated by scripts/generate_intrinsic_models.py\n"
        f"// Models: {len(models)}\n\n"
    )
    output = header + "\n".join(models)
    output = format_output(
        output, os.path.join(args.cbmc_root, GENERATED_LIBRARY))

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Generated {len(models)} models -> {args.output}",
              file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
