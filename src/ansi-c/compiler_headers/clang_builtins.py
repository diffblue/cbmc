#!/usr/bin/env python3
#
# Download Clang builtin declarations from the llvm-project git repository and
# parse them to generate declarations to use from within our C front-end.

import re
import requests
import sys


prefix_map = {
        'I': '',
        'N': '',
        'O': 'long long',
        'S': 'signed',
        'U': 'unsigned',
        'W': 'int64_t',
        'Z': 'int32_t'
        }

# we don't support:
# G -> id (Objective-C)
# H -> SEL (Objective-C)
# M -> struct objc_super (Objective-C)
# q -> Scalable vector, followed by the number of elements and base type
# E -> ext_vector, followed by the number of elements and base type
# A -> "reference" to __builtin_va_list
typespec_map = {
        'F': 'const CFString',
        'J': 'jmp_buf',
        'K': 'ucontext_t',
        'P': 'FILE',
        'Y': 'ptrdiff_t',
        'a': '__builtin_va_list',
        'b': '_Bool',
        'c': 'char',
        'd': 'double',
        'f': 'float',
        'h': '__fp16',
        'i': 'int',
        'p': 'pid_t',
        's': 'short',
        'v': 'void',
        'w': 'wchar_t',
        'x': '_Float16',
        'y': '__bf16',
        'z': '__CPROVER_size_t'
        }

# we don't support:
# & -> reference (optionally followed by an address space number)
modifier_map = {'C': 'const', 'D': 'volatile', 'R': 'restrict'}

# declarations as found in ansi-c/gcc_builtin_headers_types.h
vector_map = {
        'char': {
            8: '__gcc_v8qi',
            16: '__gcc_v16qi',
            32: '__gcc_v32qi',
            64: '__gcc_v64qi'
            },
        'unsigned char': {
            1024: '__tile'
            },
        'short': {
            4: '__gcc_v4hi',
            8: '__gcc_v8hi',
            16: '__gcc_v16hi',
            32: '__gcc_v32hi'
            },
        # new
        'unsigned short': {
            8: '__gcc_v8uhi',
            16: '__gcc_v16uhi',
            32: '__gcc_v32uhi',
            },
        'int': {
            2: '__gcc_v2si',
            4: '__gcc_v4si',
            8: '__gcc_v8si',
            16: '__gcc_v16si',
            256: '__gcc_v256si'
            },
        # new
        'unsigned int': {
            4: '__gcc_v4usi',
            8: '__gcc_v8usi',
            16: '__gcc_v16usi',
            },
        'long long int': {
            1: '__gcc_v1di',
            2: '__gcc_v2di',
            4: '__gcc_v4di',
            8: '__gcc_v8di'
            },
        # new
        'unsigned long long int': {
            2: '__gcc_v2udi',
            4: '__gcc_v4udi',
            8: '__gcc_v8udi',
            },
        # new
        '_Float16': {
            8: '__gcc_v8hf',
            16: '__gcc_v16hf',
            32: '__gcc_v32hf'
            },
        'float': {
            2: '__gcc_v2sf',
            4: '__gcc_v4sf',
            8: '__gcc_v8sf',
            16: '__gcc_v16sf'
            },
        'double': {
            2: '__gcc_v2df',
            4: '__gcc_v4df',
            8: '__gcc_v8df'
            }
        }


def parse_prefix(types, i):
    prefix = []
    while i < len(types):
        p = types[i]
        if i + 3 < len(types) and types[i:i+4] == 'LLLi':
            prefix.append('__int128_t')
            i += 4
        elif i + 1 < len(types) and types[i:i+2] == 'LL':
            prefix.extend(['long', 'long'])
            i += 2
        elif p == 'L':
            prefix.append('long')
            i += 1
        elif i + 1 < len(types) and types[i:i+2] == 'SJ':
            break
        elif i + 1 < len(types) and (
                types[i:i+2] == 'Wi' or types[i:i+2] == 'Zi'):
            prefix.append(prefix_map[p])
            i += 2
        elif prefix_map.get(p) is not None:
            mapped = prefix_map[p]
            if len(mapped):
                prefix.append(prefix_map[p])
            i += 1
        else:
            break

    return prefix, i


def build_type_inner(types, i):
    (typespec, i) = parse_prefix(types, i)

    if i < len(types):
        t = types[i]
        if i + 2 < len(types) and t == 'V':
            m = re.match(r'(\d+).*', types[i+1:])
            if m and i + 1 + len(m[1]) < len(types):
                (elem_type_list, next_i) = build_type_inner(
                        types, i + 1 + len(m[1]))
                elem_type = ' '.join(elem_type_list)
                if vector_map.get(elem_type):
                    typespec.append(vector_map[elem_type][int(m[1])])
                    i = next_i
        elif i + 1 < len(types) and t == 'X' and (
                typespec_map.get(types[i + 1])):
            typespec.append(typespec_map[types[i + 1]])
            typespec_map.append('_Complex')
            i += 2
        elif i + 1 < len(types) and types[i:i+2] == 'SJ':
            typespec.append('sigjmp_buf')
            i += 2
        elif t == '.' and i + 1 == len(types):
            typespec.append('...')
            i += 1
        elif typespec_map.get(t):
            typespec.append(typespec_map[t])
            i += 1

    return typespec, i


def build_type(types, i):
    (typespec, i) = build_type_inner(types, i)

    while i < len(types):
        s = types[i]
        if s == '*':
            typespec.append('*')
            i += 1
        elif modifier_map.get(s):
            typespec.insert(0, modifier_map[s])
            i += 1
        else:
            break

    return ' '.join(typespec), i


def process_line(name, types, attributes):
    """
    Process the macro declaring "name" as specified at the top of
    https://github.com/llvm/llvm-project/blob/main/clang/include/clang/Basic/Builtins.def
    We don't yet parse attributes.
    """

    type_specs = []
    i = 0
    while i < len(types):
        (t, i_updated) = build_type(types, i)
        assert i_updated > i, ('failed to parse type spec of' + name + ': ' +
                               types[i:])
        i = i_updated
        type_specs.append(t)

    assert len(type_specs), 'missing return type in ' + types
    if len(type_specs) == 1:
        type_specs.append('void')
    return type_specs[0] + ' ' + name + '(' + ', '.join(type_specs[1:]) + ');'


def process(input_lines):
    declarations = {}
    for l in input_lines:
        m = re.match(r'BUILTIN\((\w+),\s*"(.+)",\s*"(.*)"\)', l)
        if m:
            declaration = process_line(m[1], m[2], m[3])
            if not declarations.get('clang'):
                declarations['clang'] = {}
            declarations['clang'][m[1]] = declaration
            continue
        m = re.match(
                r'TARGET_BUILTIN\((\w+),\s*"(.+)",\s*"(.*)",\s*"(.*)"\)', l)
        if m:
            declaration = process_line(m[1], m[2], m[3])
            group = m[4]
            if len(group) == 0:
                group = 'clang'
            if not declarations.get(group):
                declarations[group] = {}
            declarations[group][m[1]] = declaration

    return declarations


def print_declarations(declaration_map, known_declarations):
    for k, v in sorted(declaration_map.items()):
        new_decls = []
        conflicting_decls = []
        for name, decl in sorted(v.items()):
            known_decl = known_declarations.get(name)
            if not known_decl:
                new_decls.append(decl)
            elif known_decl.replace(' ', '') != decl.replace(' ', ''):
                conflicting_decls.append(decl + ' // old decl: ' + known_decl)
        if len(new_decls) + len(conflicting_decls):
            print('// ' + k)
            for decl in new_decls:
                print(decl)
            for decl in conflicting_decls:
                print(decl)


def read_declarations():
    known_declarations = {}
    for fname in sys.argv[1:]:
        with open(fname) as f:
            lines = f.readlines()
            for l in lines:
                m = re.match(r'.* (\w+)\(.*\);', l)
                if m:
                    known_declarations[m[1]] = m[0]

    return known_declarations


def main():
    known_declarations = read_declarations()
    base_url = ('https://raw.githubusercontent.com/llvm/llvm-project/' +
                'main/clang/include/clang/Basic/')
    files = ['BuiltinsX86.def', 'BuiltinsX86_64.def']
    declaration_map = {}
    for f in files:
        url = base_url + f
        lines = requests.get(base_url + f).text.split('\n')
        for k, v in process(lines).items():
            if not declaration_map.get(k):
                declaration_map[k] = v
            else:
                declaration_map[k].update(v)

    print_declarations(declaration_map, known_declarations)


if __name__ == "__main__":
    main()
