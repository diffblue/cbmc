#!/usr/bin/env python3
"""Differential struct-layout fuzzer: native compiler vs CBMC.

Generates random C (or C++) translation units full of structs -- bit-fields
of mixed widths, enums with fixed underlying types, packed/aligned
attributes, arrays, nested structs and unions -- compiles them with the
native compiler to learn sizeof/alignof/offsetof of every struct and member,
and then asks CBMC to verify assertions on the same values.  Any assertion
CBMC fails (or refuses to type-check) is a layout divergence; the offending
translation unit is kept for reduction.

Usage:
  scripts/layout_fuzz.py [--cbmc BIN] [--cc gcc] [--cxx] [--seed N]
                         [--iterations N] [--structs N] [--keep DIR]

Both wall-clock time and memory of every CBMC run are bounded.
"""

import argparse
import os
import random
import subprocess
import sys
import tempfile

SCALARS = [
    ("char", 1), ("signed char", 1), ("unsigned char", 1),
    ("short", 2), ("unsigned short", 2),
    ("int", 4), ("unsigned", 4),
    ("long", 8), ("unsigned long", 8), ("long long", 8),
    ("float", 4), ("double", 8),
    ("void *", 8), ("bool", 1),
]
BITFIELD_BASES = [
    ("unsigned char", 8), ("signed char", 8), ("unsigned short", 16),
    ("short", 16), ("unsigned", 32), ("int", 32), ("unsigned long", 64),
    ("bool", 1),
]
ENUM_BASES = ["unsigned char", "signed char", "unsigned short", "short",
              "int", "unsigned", "long", "unsigned long"]


class Gen:
    def __init__(self, rng, cxx):
        self.rng = rng
        self.cxx = cxx
        self.decls = []
        self.structs = []  # (name, [member names], is_union, has_bases)
        self.enums = []    # (name, base, bits)
        self.typedefs = []  # names of typedef'd (possibly aligned) types
        self.counter = 0

    def fresh(self, prefix):
        self.counter += 1
        return "%s%d" % (prefix, self.counter)

    def attr(self, kind):
        # GNU attributes: packed / aligned / both; kept simple and
        # unambiguous between gcc and clang.
        r = self.rng.random()
        if r < 0.55:
            return ""
        if r < 0.75:
            return " __attribute__((packed))"
        if r < 0.90:
            return " __attribute__((aligned(%d)))" % self.rng.choice([2, 4, 8, 16])
        return " __attribute__((packed, aligned(%d)))" % self.rng.choice([2, 4, 8, 16])

    def gen_enum(self):
        name = self.fresh("E")
        base = self.rng.choice(ENUM_BASES)
        if self.cxx and self.rng.random() < 0.5:
            self.decls.append("enum class %s : %s { %s_A = 0, %s_B = 1, %s_C = 3 };"
                              % (name, base, name, name, name))
            self.enums.append((name, base, True))
        else:
            self.decls.append("enum %s : %s { %s_A = 0, %s_B = 1, %s_C = 3 };"
                              % (name, base, name, name, name))
            self.enums.append(("enum " + name if not self.cxx else name, base, False))

    def gen_typedef(self):
        # GCC: aligned(n) in a typedef sets the alignment exactly (either way)
        name = self.fresh("T")
        if self.structs and self.rng.random() < 0.4:
            s = self.rng.choice(self.structs)
            base = self.type_name(s)
        else:
            base = self.rng.choice(SCALARS)[0]
        attr = ""
        if self.rng.random() < 0.7:
            attr = " __attribute__((aligned(%d)))" % self.rng.choice([1, 2, 4, 8, 16])
        self.decls.append("typedef %s%s %s;" % (base, attr, name))
        self.typedefs.append(name)

    def member_type(self, depth):
        r = self.rng.random()
        if r < 0.40 or depth > 2:
            return self.rng.choice(SCALARS)[0], None
        if r < 0.50 and self.typedefs:
            return self.rng.choice(self.typedefs), None
        if r < 0.60 and self.enums:
            e = self.rng.choice(self.enums)
            return e[0], None
        if r < 0.80 and self.structs:
            s = self.rng.choice(self.structs)
            return ("%s %s" % ("union" if s[2] else "struct", s[0])) if not self.cxx else s[0], None
        # array of scalar
        return self.rng.choice(SCALARS)[0], self.rng.choice([1, 2, 3, 5, 8])

    def alignas_spec(self):
        # alignas / _Alignas must not be weaker than the natural alignment
        # ([dcl.align]/5), so only large values are generated
        return ("alignas(%d) " if self.cxx else "_Alignas(%d) ") % self.rng.choice([16, 32])

    def gen_anonymous_member(self, lines, members):
        # C11 [6.7.2.1]/13 / GNU: an anonymous struct or union member; its
        # members are accessed as if they were members of the enclosing type
        key = "union" if self.rng.random() < 0.5 else "struct"
        inner = []
        for _ in range(self.rng.randint(1, 3)):
            m = self.fresh("a")
            t, arr = self.member_type(3)
            if arr:
                inner.append("    %s %s[%d];" % (t, m, arr))
            else:
                inner.append("    %s %s;" % (t, m))
            members.append((m, False))
        lines.append("  %s\n  {\n%s\n  }%s;" % (key, "\n".join(inner), self.attr(key)))

    def gen_struct(self, depth=0):
        is_union = self.rng.random() < 0.15
        name = self.fresh("U" if is_union else "S")
        members = []
        lines = []
        bases = []
        # C++: base classes (including empty ones; [class.mem], Itanium ABI
        # base-subobject layout).  Unions cannot have bases.
        if self.cxx and not is_union and self.rng.random() < 0.3:
            candidates = [b for b in self.structs if not b[2] and not b[3]]
            if self.rng.random() < 0.4:
                empty = self.fresh("EB")
                self.decls.append("struct %s {};" % empty)
                bases.append(empty)
            for b in self.rng.sample(candidates, min(len(candidates), self.rng.randint(1, 2))):
                bases.append(b[0])
        n = self.rng.randint(1, 7)
        for _ in range(n):
            m = self.fresh("m")
            r = self.rng.random()
            if r < 0.06 and not is_union:
                self.gen_anonymous_member(lines, members)
                continue
            if r < 0.45:
                # bit-field
                if self.rng.random() < 0.3 and self.enums:
                    e = self.rng.choice(self.enums)
                    bits_avail = {"unsigned char": 8, "signed char": 8,
                                  "unsigned short": 16, "short": 16, "int": 32,
                                  "unsigned": 32, "long": 64,
                                  "unsigned long": 64}[e[1]]
                    width = self.rng.randint(2, min(bits_avail, 9))
                    lines.append("  %s %s : %d;" % (e[0], m, width))
                else:
                    base, maxw = self.rng.choice(BITFIELD_BASES)
                    width = self.rng.randint(1, maxw)
                    if self.rng.random() < 0.08:
                        lines.append("  %s : 0;" % base)  # zero-width, unnamed
                        continue
                    lines.append("  %s %s : %d;" % (base, m, width))
                members.append((m, True))
            else:
                t, arr = self.member_type(depth)
                member_attr = ""
                prefix = ""
                if self.rng.random() < 0.15:
                    member_attr = " __attribute__((aligned(%d)))" % self.rng.choice([2, 4, 8, 16])
                    if self.rng.random() < 0.5:
                        member_attr = " __attribute__((packed, aligned(%d)))" % self.rng.choice([1, 2, 4])
                elif self.rng.random() < 0.08:
                    prefix = self.alignas_spec()
                if arr:
                    lines.append("  %s%s %s[%d]%s;" % (prefix, t, m, arr, member_attr))
                else:
                    lines.append("  %s%s %s%s;" % (prefix, t, m, member_attr))
                members.append((m, False))
        if self.cxx:
            self.gen_non_storage_members(name, lines, is_union)
        key = "union" if is_union else "struct"
        head = "%s %s" % (key, name)
        trailing = self.attr(key)
        if self.cxx and self.rng.random() < 0.08:
            head = "%s alignas(%d) %s" % (key, self.rng.choice([16, 32]), name)
            # g++ lets a trailing `aligned(k)' override a class-head alignas;
            # clang and N5008 [dcl.align]/4 take the strictest.  Do not
            # generate the combination (a known, deliberate divergence).
            if "aligned" in trailing:
                trailing = ""
        if bases:
            head += " : " + ", ".join("public " + b for b in bases)
        decl = "%s\n{\n%s\n}%s;" % (head, "\n".join(lines), trailing)
        # #pragma pack(n) around some declarations (GCC/MSVC extension:
        # member alignment capped at n)
        if self.rng.random() < 0.12:
            n_pack = self.rng.choice([1, 2, 4, 8])
            decl = "#pragma pack(push, %d)\n%s\n#pragma pack(pop)" % (n_pack, decl)
        self.decls.append(decl)
        self.structs.append((name, members, is_union, bool(bases)))

    def gen_non_storage_members(self, name, lines, is_union):
        # N5008 [class.mem]: member typedefs/alias-declarations, static data
        # members and member functions are members but not subobjects -- they
        # must not take part in the layout.  A user-declared constructor makes
        # the class a non-POD (C++03 [class]/9), which changes the tail-padding
        # rule for base subobjects and GCC's packed rule for members of that
        # type.  Insert them at random positions between the data members.
        extras = []
        if self.rng.random() < 0.35:
            t = self.rng.choice(SCALARS)[0]
            if self.rng.random() < 0.5:
                extras.append("  using %s = %s;" % (self.fresh("vt"), t))
            else:
                extras.append("  typedef %s %s;" % (t, self.fresh("td")))
        if self.rng.random() < 0.3 and not is_union:
            t = self.rng.choice(SCALARS)[0]
            if self.rng.random() < 0.5:
                extras.append("  static constexpr %s %s = 0;" % (t, self.fresh("k")))
            else:
                extras.append("  static %s %s;" % (t, self.fresh("s")))
        if self.rng.random() < 0.3:
            extras.append("  int %s() const { return 1; }" % self.fresh("f"))
        if self.rng.random() < 0.25 and not is_union:
            # a user-provided default constructor: the class is a non-POD
            extras.append("  %s() {}" % name)
        for e in extras:
            lines.insert(self.rng.randint(0, len(lines)), e)

    def type_name(self, s):
        if self.cxx:
            return s[0]
        return "%s %s" % ("union" if s[2] else "struct", s[0])


def native_values(gen, cc, cxx, workdir):
    """Compile+run a probe printing sizeof/alignof/offsetof of everything."""
    lines = ["#include <stddef.h>", "#include <stdio.h>"]
    if not cxx:
        lines.append("#include <stdbool.h>")
    lines += gen.decls
    lines.append("int main(void)\n{")
    for s in gen.structs:
        tn = gen.type_name(s)
        lines.append('  printf("%s %%zu %%zu\\n", sizeof(%s), %s(%s));'
                     % (s[0], tn, "alignof" if cxx else "_Alignof", tn))
        for m, is_bf in s[1]:
            if is_bf:
                continue
            lines.append('  printf("%s.%s %%zu\\n", offsetof(%s, %s));' % (s[0], m, tn, m))
    lines.append("  return 0;\n}")
    src = os.path.join(workdir, "probe.%s" % ("cpp" if cxx else "c"))
    with open(src, "w") as f:
        f.write("\n".join(lines) + "\n")
    exe = os.path.join(workdir, "probe")
    std = ["-std=gnu++17"] if cxx else ["-std=gnu11"]
    r = subprocess.run([cc] + std + ["-w", "-o", exe, src],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr
    out = subprocess.run([exe], capture_output=True, text=True).stdout
    values = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3:
            values[parts[0]] = (int(parts[1]), int(parts[2]))
        elif len(parts) == 2:
            values[parts[0]] = int(parts[1])
    return values, None


def cbmc_unit(gen, values, cxx, workdir):
    lines = ["#include <stddef.h>"]
    if cxx:
        lines.append('extern "C" void __CPROVER_assert(bool, const char *);')
    else:
        lines.append("#include <stdbool.h>")
    lines += gen.decls
    lines.append("int main(void)\n{")
    for s in gen.structs:
        tn = gen.type_name(s)
        size, align = values[s[0]]
        lines.append('  __CPROVER_assert(sizeof(%s) == %d, "sizeof %s == %d");'
                     % (tn, size, s[0], size))
        lines.append('  __CPROVER_assert(%s(%s) == %d, "alignof %s == %d");'
                     % ("alignof" if cxx else "_Alignof", tn, align, s[0], align))
        for m, is_bf in s[1]:
            if is_bf:
                continue
            off = values["%s.%s" % (s[0], m)]
            lines.append('  __CPROVER_assert(offsetof(%s, %s) == %d, "offsetof %s.%s == %d");'
                         % (tn, m, off, s[0], m, off))
    lines.append("  return 0;\n}")
    src = os.path.join(workdir, "unit.%s" % ("cpp" if cxx else "c"))
    with open(src, "w") as f:
        f.write("\n".join(lines) + "\n")
    return src


def run_cbmc(cbmc, src, cxx, timeout, mem_kib):
    cmd = "ulimit -v %d; exec timeout %d %s %s %s" % (
        mem_kib, timeout, cbmc, "--cpp17" if cxx else "", src)
    r = subprocess.run(["sh", "-c", cmd], capture_output=True, text=True)
    out = r.stdout + r.stderr
    failures = [l for l in out.splitlines() if l.endswith(": FAILURE")]
    conversion_error = "CONVERSION ERROR" in out or "PARSING ERROR" in out
    return r.returncode, failures, conversion_error, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cbmc", default="build-work/bin/cbmc")
    ap.add_argument("--cc", default=None, help="native compiler (gcc / g++)")
    ap.add_argument("--cxx", action="store_true", help="generate C++")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--iterations", type=int, default=50)
    ap.add_argument("--structs", type=int, default=6)
    ap.add_argument("--keep", default="layout-fuzz-failures")
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--mem-kib", type=int, default=8000000)
    args = ap.parse_args()
    cc = args.cc or ("g++" if args.cxx else "gcc")
    os.makedirs(args.keep, exist_ok=True)
    divergences = 0
    for it in range(args.iterations):
        seed = args.seed + it
        rng = random.Random(seed)
        gen = Gen(rng, args.cxx)
        for _ in range(rng.randint(1, 3)):
            gen.gen_enum()
        for i in range(args.structs):
            gen.gen_struct()
            if rng.random() < 0.5:
                gen.gen_typedef()
        with tempfile.TemporaryDirectory() as wd:
            values, err = native_values(gen, cc, args.cxx, wd)
            if values is None:
                print("seed %d: native compile failed (skipped): %s"
                      % (seed, err.strip().splitlines()[0] if err.strip() else ""))
                continue
            src = cbmc_unit(gen, values, args.cxx, wd)
            rc, failures, conv, out = run_cbmc(args.cbmc, src, args.cxx,
                                               args.timeout, args.mem_kib)
            if failures or conv or rc not in (0, 10):
                divergences += 1
                dst = os.path.join(args.keep, "seed%d.%s" % (seed, "cpp" if args.cxx else "c"))
                with open(src) as f:
                    body = f.read()
                with open(dst, "w") as f:
                    f.write(body)
                with open(dst + ".log", "w") as f:
                    f.write(out)
                what = "conversion error" if conv else ("%d failing" % len(failures))
                print("seed %d: DIVERGENCE (%s) -> %s" % (seed, what, dst))
                for l in failures[:4]:
                    print("    " + l.strip())
            else:
                print("seed %d: ok" % seed)
    print("%d divergence(s) in %d iterations" % (divergences, args.iterations))
    return 1 if divergences else 0


if __name__ == "__main__":
    sys.exit(main())
