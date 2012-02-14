#!/bin/bash

set -e

if [ -e gcc-builtins.h ] ; then
  echo "gcc-builtins.h already exists" 1>&2
  exit 1
fi

svn export http://gcc.gnu.org/svn/gcc/trunk/gcc/builtin-types.def > /dev/null
svn export http://gcc.gnu.org/svn/gcc/trunk/gcc/builtins.def > /dev/null
svn export http://gcc.gnu.org/svn/gcc/trunk/gcc/sync-builtins.def > /dev/null
svn export http://gcc.gnu.org/svn/gcc/trunk/gcc/omp-builtins.def > /dev/null
svn export http://gcc.gnu.org/svn/gcc/trunk/gcc/gtm-builtins.def > /dev/null


cat > gcc-builtins.h <<EOF
#include <inttypes.h>
#include <complex.h>
#include <unistd.h>
#include <stdio.h>
#include <wctype.h>

EOF

cat > builtins.h <<EOF
#define void_type_node void
#define ptr_type_node void*
#define const_ptr_type_node const void*
#define boolean_type_node _Bool
#define integer_type_node int
#define integer_ptr_type_node int*
#define unsigned_type_node unsigned
#define long_integer_type_node long
#define long_unsigned_type_node unsigned long
#define long_long_integer_type_node long long
#define long_long_unsigned_type_node unsigned long long
#define size_type_node size_t
#define signed_size_type_node ssize_t
#define intmax_type_node intmax_t
#define uintmax_type_node uintmax_t
#define string_type_node char*
#define const_string_type_node const char*
#define double_type_node double
#define double_ptr_type_node double*
#define complex_double_type_node double complex
#define float_type_node float
#define float_ptr_type_node float*
#define complex_float_type_node float complex
#define long_double_type_node long double
#define long_double_ptr_type_node long double*
#define complex_long_double_type_node long double complex
#define fileptr_type_node FILE*
#define va_list_arg_type_node va_list
#define va_list_ref_type_node va_list
#define wint_type_node wint_t
#define uint32_type_node uint32_t
#define uint64_type_node uint64_t
#define pid_type_node pid_t

// some newer versions of GCC apparently support __floatXYZ
#define dfloat32_type_node __float32
#define dfloat64_type_node __float64
#define dfloat128_type_node __float128

#define build_qualified_type(t, q) q t
#define build_pointer_type(t) t*
#define TYPE_QUAL_VOLATILE volatile

#define DEF_PRIMITIVE_TYPE(ENUM, TYPE) \
NEXTDEF ENUM TYPE
#define DEF_FUNCTION_TYPE_0(ENUM, RETURN) \
NEXTDEF ENUM(name) RETURN name()
#define DEF_FUNCTION_TYPE_1(ENUM, RETURN, ARG1) \
NEXTDEF ENUM(name) RETURN name(ARG1)
#define DEF_FUNCTION_TYPE_2(ENUM, RETURN, ARG1, ARG2) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2)
#define DEF_FUNCTION_TYPE_3(ENUM, RETURN, ARG1, ARG2, ARG3) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3)
#define DEF_FUNCTION_TYPE_4(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4)
#define DEF_FUNCTION_TYPE_5(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5)
#define DEF_FUNCTION_TYPE_6(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6)
#define DEF_FUNCTION_TYPE_7(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7)

#define DEF_FUNCTION_TYPE_VAR_0(ENUM, RETURN) \
NEXTDEF ENUM(name) /* RETURN name(...) -- this is a macro */
#define DEF_FUNCTION_TYPE_VAR_1(ENUM, RETURN, ARG1) \
NEXTDEF ENUM(name) RETURN name(ARG1, ...)
#define DEF_FUNCTION_TYPE_VAR_2(ENUM, RETURN, ARG1, ARG2) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ...)
#define DEF_FUNCTION_TYPE_VAR_3(ENUM, RETURN, ARG1, ARG2, ARG3) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ...)
#define DEF_FUNCTION_TYPE_VAR_4(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ...)
#define DEF_FUNCTION_TYPE_VAR_5(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ...)

#define DEF_POINTER_TYPE(ENUM, TYPE) \
NEXTDEF ENUM TYPE*

#include "builtin-types.def"

NEXTDEF DEF_BUILTIN(ENUM, NAME, CLASS, TYPE, LIBTYPE, BOTH_P, \
                  FALLBACK_P, NONANSI_P, ATTRS, IMPLICIT, COND) \
TYPE(MANGLE(NAME));
EOF

gcc -E builtins.h | sed 's/^NEXTDEF/#define/' | cat - builtins.def | \
  gcc -E -P - | \
  sed 's/MANGLE("__builtin_" "\(.*\)")/__builtin_\1/' | \
  sed '/^;$/d' >> gcc-builtins.h

rm builtin-types.def builtins.def sync-builtins.def omp-builtins.def gtm-builtins.def
rm builtins.h

# for some we don't know how to handle them - removing symbols should be safe
sed -i '/MANGLE/d' gcc-builtins.h
sed -i '/builtin_type_for_size/d' gcc-builtins.h
sed -i '/BT_FN/d' gcc-builtins.h
sed -i '/lang_hooks.types.type_for_mode/d' gcc-builtins.h
sed -i '/__float/d' gcc-builtins.h

cat gcc-builtins.h | sed 's/__builtin/XX__builtin/' | \
  gcc -c -fno-builtin -x c - -o gcc-builtins.o
rm gcc-builtins.o
echo "Successfully built gcc-builtins.h"

