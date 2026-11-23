#!/usr/bin/env python3
"""Differential tests of CBMC's inline-assembly semantics against hardware.

Each test case is a small C function containing one inline assembly
statement. The function is compiled with the native or a cross compiler and
executed (natively on x86-64, with the Unicorn emulator for AArch64 and
AArch32) on several input vectors. The observed results become the expected
values of a CBMC regression test, which asserts that CBMC computes exactly
those results, i.e. that the statement is interpreted, not approximated.

Usage:
  asm_differential.py ARCH OUTPUT_DIR

ARCH is x86_64, aarch64 or arm. Requirements: gcc (x86_64),
aarch64-linux-gnu-gcc (aarch64), clang (arm), and the Python package unicorn
(pip install unicorn) for the emulated architectures.
"""

import os
import random
import shutil
import struct
import subprocess
import sys
import tempfile

import asm_differential_cases as cases_module

MASK64 = (1 << 64) - 1

# the first lines of the generated test, by architecture
HEADERS = {
    'x86_64': [
        '// x86 inline assembly that is interpreted exactly. The expected '
        'values were',
        '// observed on x86-64 hardware.'],
    'aarch64': [
        '// AArch64 inline assembly that is interpreted exactly. The expected '
        'values were',
        '// observed with an emulator.'],
    'arm': [
        '// AArch32 inline assembly (A32 code) that is interpreted exactly. '
        'The expected',
        '// values were observed with an emulator.'],
}


def have(tool):
    """Whether tool is on the PATH."""
    return shutil.which(tool) is not None


def c_literal(value):
    return '0x%xULL' % (value & MASK64)


def function_source(index, case):
    """The C function of a test case: load variables from io, run the
    statement, store them back."""
    lines = ['void asm_case_%d(unsigned long long *io)' % index, '{']
    k = 0
    for ctype, name, length in case.variables:
        if length is None:
            lines.append('  %s %s = (%s)io[%d];' % (ctype, name, ctype, k))
            k += 1
        else:
            lines.append('  %s %s[%d];' % (ctype, name, length))
            for i in range(length):
                lines.append('  %s[%d] = (%s)io[%d];' % (name, i, ctype, k))
                k += 1
    if case.prologue:
        lines.append('  ' + case.prologue)
    lines.append('  ' + case.statement)
    k = 0
    for ctype, name, length in case.variables:
        if length is None:
            lines.append('  io[%d] = (unsigned long long)%s;' % (k, name))
            k += 1
        else:
            for i in range(length):
                lines.append(
                    '  io[%d] = (unsigned long long)%s[%d];' % (k, name, i))
                k += 1
    lines.append('}')
    return '\n'.join(lines) + '\n'


def slots(case):
    return sum(1 if length is None else length
               for _, _, length in case.variables)


def input_vectors(case, count, seed):
    cap = os.environ.get('ASM_DIFF_MAX_VECTORS')
    if cap is not None:
        count = min(count, int(cap))
    rng = random.Random(seed)
    vectors = list(case.inputs)
    edges = [0, 1, 2, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff,
             0x7fffffffffffffff, 0x8000000000000000, MASK64]
    while len(vectors) < count:
        vector = []
        for _ in range(slots(case)):
            vector.append(rng.choice(edges) if rng.random() < 0.3
                          else rng.getrandbits(64))
        if case.constrain is not None:
            vector = case.constrain(vector)
        vectors.append(vector)
    return vectors


def run_x86_64(sources, vectors, workdir):
    driver = ['#include <stdio.h>']
    driver += sources
    driver.append('int main(void)\n{')
    driver.append('  unsigned long long io[64];')
    for index, case_vectors in enumerate(vectors):
        for vector in case_vectors:
            for k, value in enumerate(vector):
                driver.append('  io[%d] = %s;' % (k, c_literal(value)))
            driver.append('  asm_case_%d(io);' % index)
            driver.append(
                '  for(int i = 0; i < %d; ++i) printf("%%llx ", io[i]);'
                % len(vector))
            driver.append('  printf("\\n");')
    driver.append('  return 0;\n}')
    path = os.path.join(workdir, 'native.c')
    with open(path, 'w') as f:
        f.write('\n'.join(driver))
    exe = os.path.join(workdir, 'native')
    subprocess.check_call(['gcc', '-O1', '-o', exe, path])
    out = subprocess.check_output([exe], text=True).split('\n')
    results = []
    line = 0
    for case_vectors in vectors:
        case_results = []
        for _ in case_vectors:
            case_results.append([int(x, 16) for x in out[line].split()])
            line += 1
        results.append(case_results)
    return results


def run_emulated(arch, cases, sources, vectors, workdir):
    import unicorn
    from unicorn import arm64_const, arm_const
    from elftools.elf.elffile import ELFFile

    path = os.path.join(workdir, 'cases.c')
    with open(path, 'w') as f:
        f.write('\n'.join(sources))
    obj = os.path.join(workdir, 'cases.o')
    if arch == 'aarch64':
        flags = ['-O1', '-ffreestanding', '-fno-pic', '-march=armv8.1-a', '-c',
                 '-o', obj, path]
        if have('aarch64-linux-gnu-gcc'):
            subprocess.check_call(['aarch64-linux-gnu-gcc'] + flags)
        else:
            subprocess.check_call(
                ['clang', '--target=aarch64-linux-gnu'] + flags)
    else:
        subprocess.check_call(
            ['clang', '--target=armv7a-none-eabi', '-marm', '-O1',
             '-ffreestanding', '-mfloat-abi=soft', '-c', '-o', obj, path])

    # Read the code and the function offsets straight from the ELF object, so
    # that no architecture-specific objcopy/nm is needed.
    with open(obj, 'rb') as f:
        elf = ELFFile(f)
        text_section = elf.get_section_by_name('.text')
        # the code is used as it is, so it must not need relocation
        for name in ('.rel.text', '.rela.text'):
            relocations = elf.get_section_by_name(name)
            if relocations is not None and relocations.num_relocations():
                sys.exit('the cases need relocations, which are not applied')
        code = text_section.data()
        text_addr = text_section['sh_addr']
        symbols = {}
        symtab = elf.get_section_by_name('.symtab')
        for symbol in symtab.iter_symbols():
            if symbol['st_info']['type'] == 'STT_FUNC':
                symbols[symbol.name] = symbol['st_value'] - text_addr

    code_base, data_base, stack_base, stop = 0x100000, 0x200000, 0x300000, \
        0x400000
    results = []
    for index, case_vectors in enumerate(vectors):
        case_results = []
        for vector in case_vectors:
            if arch == 'aarch64':
                uc = unicorn.Uc(unicorn.UC_ARCH_ARM64, unicorn.UC_MODE_ARM)
                uc.ctl_set_cpu_model(arm64_const.UC_CPU_ARM64_MAX)
            else:
                uc = unicorn.Uc(unicorn.UC_ARCH_ARM, unicorn.UC_MODE_ARM)
            uc.mem_map(code_base, 0x100000)
            uc.mem_map(data_base, 0x10000)
            uc.mem_map(stack_base, 0x10000)
            uc.mem_map(stop, 0x1000)
            uc.mem_write(code_base, code)
            uc.mem_write(data_base, b''.join(
                struct.pack('<Q', v & MASK64) for v in vector))
            start = code_base + symbols['asm_case_%d' % index]
            if arch == 'aarch64':
                uc.reg_write(arm64_const.UC_ARM64_REG_X0, data_base)
                uc.reg_write(arm64_const.UC_ARM64_REG_LR, stop)
                uc.reg_write(arm64_const.UC_ARM64_REG_SP, stack_base + 0x8000)
            else:
                uc.reg_write(arm_const.UC_ARM_REG_R0, data_base)
                uc.reg_write(arm_const.UC_ARM_REG_LR, stop)
                uc.reg_write(arm_const.UC_ARM_REG_SP, stack_base + 0x8000)
            uc.emu_start(start, stop, count=100000)
            pc = uc.reg_read(arm64_const.UC_ARM64_REG_PC if arch == 'aarch64'
                             else arm_const.UC_ARM_REG_PC)
            if pc != stop:
                sys.exit('%s, vector %s: emulation did not return'
                         % (cases[index].name, vector))
            data = uc.mem_read(data_base, 8 * len(vector))
            case_results.append(
                [struct.unpack_from('<Q', data, 8 * i)[0]
                 for i in range(len(vector))])
        results.append(case_results)
    return results


def main():
    arch, output = sys.argv[1], sys.argv[2]
    cases = cases_module.CASES[arch]
    sources = [function_source(i, c) for i, c in enumerate(cases)]
    vectors = [input_vectors(c, c.vectors, 1000 + i)
               for i, c in enumerate(cases)]

    with tempfile.TemporaryDirectory() as workdir:
        if arch == 'x86_64':
            results = run_x86_64(sources, vectors, workdir)
        else:
            results = run_emulated(arch, cases, sources, vectors, workdir)

    os.makedirs(output, exist_ok=True)
    lines = HEADERS[arch] + [
        '// Generated by scripts/asm_differential/asm_differential.py %s.'
        % arch,
        '']
    for index, case in enumerate(cases):
        lines.append('// %s' % case.name)
        lines.append(sources[index])
    lines.append('int main(void)\n{')
    for index, case in enumerate(cases):
        for j, (vector, result) in enumerate(zip(vectors[index],
                                                 results[index])):
            lines.append('  {')
            lines.append('    unsigned long long io[%d] = {%s};' % (
                len(vector), ', '.join(c_literal(v) for v in vector)))
            lines.append('    asm_case_%d(io);' % index)
            checks = ' && '.join('io[%d] == %s' % (k, c_literal(v))
                                 for k, v in enumerate(result))
            lines.append('    __CPROVER_assert(%s, "%s, vector %d");' % (
                checks, case.name, j))
            lines.append('  }')
    lines.append('  return 0;\n}')
    # The x86 test is preprocessed source: preprocessing it for x86 would
    # fail on hosts of other architectures.
    out_path = os.path.join(
        output, 'main.i' if arch == 'x86_64' else 'main.c')
    with open(out_path, 'w') as f:
        f.write('\n'.join(lines) + '\n')

    # keep the committed test clang-format clean, if the formatter is present,
    # using the style of the repository (the output may be outside of it)
    style = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), '..', '..',
        '.clang-format')
    for formatter in ('clang-format-15', 'clang-format'):
        if have(formatter):
            subprocess.check_call(
                [formatter, '--style=file:' + os.path.normpath(style), '-i',
                 out_path])
            break


if __name__ == '__main__':
    main()
