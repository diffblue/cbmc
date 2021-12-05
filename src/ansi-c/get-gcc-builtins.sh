#!/bin/bash

set -e

if [ -e gcc-builtins.h ] ; then
  echo "gcc-builtins.h already exists" 1>&2
  exit 1
fi

builtin_defs=" \
  builtin-types.def builtins.def sync-builtins.def \
  omp-builtins.def gtm-builtins.def \
  sanitizer.def brig-builtins.def coroutine-builtins.def \
  config/i386/i386-builtin.def config/i386/i386-builtin-types.def"

for f in $builtin_defs ; do
  bn=`basename $f`
  [ ! -s $bn ] || continue
  echo Downloading git://gcc.gnu.org/git/gcc/$f
  if [ `dirname $f` = "." ] ; then
    git archive --remote=git://gcc.gnu.org/git/gcc.git HEAD:gcc/ $bn | tar -x > $bn
  else
    git archive --remote=git://gcc.gnu.org/git/gcc.git HEAD:gcc/`dirname $f`/ $bn | tar -x > $bn
  fi
done

cat > gcc-builtins.h <<EOF
#include <inttypes.h>
#include <complex.h>
#include <unistd.h>
#include <stdio.h>
#include <wctype.h>
#include <fenv.h>

typedef   char   __gcc_v8qi  __attribute__ ((__vector_size__ (8)));
typedef   char   __gcc_v16qi __attribute__ ((__vector_size__ (16)));
typedef   char   __gcc_v32qi __attribute__ ((__vector_size__ (32)));
typedef   char   __gcc_v64qi __attribute__ ((__vector_size__ (64)));
typedef   int    __gcc_v2si  __attribute__ ((__vector_size__ (8)));
typedef   int    __gcc_v4si  __attribute__ ((__vector_size__ (16)));
typedef   int    __gcc_v8si  __attribute__ ((__vector_size__ (32)));
typedef   int    __gcc_v16si  __attribute__ ((__vector_size__ (64)));
typedef   short  __gcc_v4hi  __attribute__ ((__vector_size__ (8)));
typedef   short  __gcc_v8hi  __attribute__ ((__vector_size__ (16)));
typedef   short  __gcc_v16hi __attribute__ ((__vector_size__ (32)));
typedef   short  __gcc_v32hi __attribute__ ((__vector_size__ (64)));
typedef   float  __gcc_v2sf  __attribute__ ((__vector_size__ (8)));
typedef   float  __gcc_v4sf  __attribute__ ((__vector_size__ (16)));
typedef   float  __gcc_v8sf  __attribute__ ((__vector_size__ (32)));
typedef   float  __gcc_v16sf  __attribute__ ((__vector_size__ (64)));
typedef   double __gcc_v2df  __attribute__ ((__vector_size__ (16)));
typedef   double __gcc_v4df  __attribute__ ((__vector_size__ (32)));
typedef   double __gcc_v8df  __attribute__ ((__vector_size__ (64)));
typedef   long long __gcc_v1di __attribute__ ((__vector_size__ (8)));
typedef   long long __gcc_v2di __attribute__ ((__vector_size__ (16)));
typedef   long long __gcc_v4di __attribute__ ((__vector_size__ (32)));
typedef   long long __gcc_v8di __attribute__ ((__vector_size__ (64)));
typedef   long long __gcc_di;

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
#define uint16_type_node uint16_t
#define uint32_type_node uint32_t
#define uint64_type_node uint64_t
#define pid_type_node pid_t
#define const_tm_ptr_type_node const struct tm*
#define char_type_node char
#define intSI_type_node int
#define intHI_type_node short
#define unsigned_intSI_type_node unsigned
#define unsigned_intHI_type_node unsigned short
#define unsigned_intQI_type_node unsigned char
#define short_unsigned_type_node unsigned short
#define short_integer_type_node short
#define unsigned_char_type_node unsigned char
#define fenv_t_ptr_type_node fenv_t*
#define const_fenv_t_ptr_type_node const fenv_t*
#define fexcept_t_ptr_type_node fexcept_t*
#define const_fexcept_t_ptr_type_node const fexcept_t*

// some newer versions of GCC apparently support __floatXYZ
#define dfloat32_type_node __float32
#define dfloat64_type_node __float64
#define dfloat128_type_node __CPROVER_Float128

#define build_qualified_type(t, q) q t
#define build_pointer_type(t) t*
#define TYPE_QUAL_VOLATILE volatile
#define TYPE_QUAL_CONST const

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
#define DEF_FUNCTION_TYPE_8(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8)
#define DEF_FUNCTION_TYPE_9(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8, ARG9) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8, ARG9)
#define DEF_FUNCTION_TYPE_10(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8, ARG9, ARG10) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8, ARG9, ARG10)
#define DEF_FUNCTION_TYPE_11(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8, ARG9, ARG10, ARG11) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ARG8, ARG9, ARG10, ARG11)

#define DEF_FUNCTION_TYPE_VAR_0(ENUM, RETURN) \
NEXTDEF ENUM(name) RETURN name()
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
#define DEF_FUNCTION_TYPE_VAR_6(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ...)
#define DEF_FUNCTION_TYPE_VAR_7(ENUM, RETURN, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7) \
NEXTDEF ENUM(name) RETURN name(ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7, ...)

#define DEF_POINTER_TYPE(ENUM, TYPE) \
NEXTDEF ENUM TYPE*

#define DEF_POINTER_TYPE_CONST(ENUM, TYPE, C) \
NEXTDEF ENUM const TYPE*

#include "builtin-types.def"

NEXTDEF DEF_BUILTIN(ENUM, NAME, CLASS, TYPE, LIBTYPE, BOTH_P, \
                  FALLBACK_P, NONANSI_P, ATTRS, IMPLICIT, COND) \
TYPE(MANGLE(NAME));

#include "i386-builtin-types-expanded.def"

NEXTDEF BDESC(mask, mask2, icode, name, code, comparison, flag) \
flag(MANGLEi386(name));
NEXTDEF BDESC_FIRST(kind, KIND, mask, mask2, icode, name, code, comparison, flag) \
flag(MANGLEi386(name));
EOF

grep '^DEF_VECTOR_TYPE' i386-builtin-types.def | \
  awk -F '[,() \t]' '{ print "#define " $3 " __gcc_" tolower($3) }' \
  > i386-builtin-types-expanded.def

grep -v '^DEF_FUNCTION_TYPE[[:space:]]' i386-builtin-types.def | \
  grep '^DEF_P' | \
  sed '/^DEF_POINTER_TYPE[^,]*, [^,]*, [^,]*$/ s/_TYPE/_TYPE_CONST/' \
  >> i386-builtin-types-expanded.def

cat i386-builtin-types.def | \
  sed '/^DEF_FUNCTION_TYPE[[:space:]]/! s/.*//' | \
  sed 's/^DEF_FUNCTION_TYPE[[:space:]]*(\([^,]*\))/\1_FTYPE_VOID/' | \
  sed 's/^DEF_FUNCTION_TYPE[[:space:]]*(\([^,]*\), \(.*\))/\1_FTYPE_\2/' | \
  sed 's/, /_/g' > i386-type-names.def
cat i386-builtin-types.def | tr -c -d ',\n' | awk '{ print length }' | \
  paste - i386-type-names.def i386-builtin-types.def | grep -v '#' | \
  sed 's/^\([0-9]\)[[:space:]]*\([^[:space:]]*\)[[:space:]]*DEF_FUNCTION_TYPE[[:space:]]*(/DEF_FUNCTION_TYPE_\1(\2, /' | \
  grep ^DEF_FUNCTION_TYPE >> i386-builtin-types-expanded.def

cat >> i386-builtin-types-expanded.def <<EOF
DEF_FUNCTION_TYPE_4(UHI_FTYPE_V16SI_V16SI_INT_UHI, UHI, V16SI, V16SI, INT, UHI)
DEF_FUNCTION_TYPE_2(UQI_FTYPE_UQI_UQI_CONST, UQI, UQI, UQI)
EOF

gcc -E builtins.h | sed 's/^NEXTDEF/#define/' | \
  cat - builtins.def i386-builtin.def | \
  sed 's/_\(COUNT\|CONVERT\|ROUND\|PTEST\|SWAP\|VEC_MERGE\))$/)/' | \
  gcc -E -P - | \
  sed 's/BT_FN_VOID_VAR\*/void (*)()/g' |
  sed 's/BT_FN_VOID_PTR\*/void (*)(void *)/g' |
  sed 's/BT_FN_VOID_PTR_PTR\*/void (*)(void *, void *)/g' |
  sed 's/MANGLE("__builtin_" "\(.*\)")/__builtin_\1/' | \
  sed 's/MANGLEi386("__builtin_\(.*\)")/__builtin_\1/' | \
  sed 's/^(int) //' | \
  sed '/^;$/d' >> gcc-builtins.h

for f in $builtin_defs builtins.h i386-builtin-types-expanded.def i386-type-names.def ; do
  rm `basename $f`
done

sed_is_gnu_sed=0
if sed --version >/dev/null 2>&1 ; then
  # GNU sed
  sed_is_gnu_sed=1
fi

# for some we don't know how to handle them - removing symbols should be safe
remove_line() {
  local pattern="$1"
  if [ $sed_is_gnu_sed -eq 1 ] ; then
    sed -i "/$pattern/d" gcc-builtins.h
  else
    sed -i '' "/$pattern/d" gcc-builtins.h
  fi
}

remove_line MANGLE
remove_line builtin_type_for_size
remove_line lang_hooks.types.type_for_mode
remove_line BT_LAST
remove_line BDESC_END
remove_line error_mark_node
remove_line '^0('
remove_line 'CC.mode('
remove_line MULTI_ARG

ifs=$IFS
IFS='
'

while read line ; do
  if [ $sed_is_gnu_sed -eq 1 ] ; then
    line=`echo "$line" | sed 's/\<size_t/__CPROVER_size_t/g'`
    line=`echo "$line" | sed 's/\<complex\>\([^\.]\)/_Complex\1/g'`
  else
    line=`echo "$line" | sed 's/[[:<:]]size_t/__CPROVER_size_t/g'`
    line=`echo "$line" | sed 's/[[:<:]]complex[[:>:]]\([^\.]\)/_Complex\1/g'`
  fi

  if grep -q -F "$line" gcc_builtin_headers_*.h ; then
    continue
  fi

  bi=`echo "$line" | cut -f1 -d'(' | sed 's/.* //'`

  if [[ $bi =~ __builtin_ia32 ]] ; then
    if grep -wq $bi gcc_builtin_headers_ia32*.h ; then
      if [ $sed_is_gnu_sed -eq 1 ] ; then
        sed -i "/^[^/].*$bi(/ s/.*/$line/" gcc_builtin_headers_ia32*.h
      else
        sed -i '' "/^[^/].*$bi(/ s/.*/$line/" gcc_builtin_headers_ia32*.h
      fi
      continue
    fi
  fi

  echo "$line" >> _gcc-builtins.h
done < gcc-builtins.h
mv _gcc-builtins.h gcc-builtins.h

cat gcc-builtins.h | sed 's/__builtin/XX__builtin/' | \
  gcc -D__CPROVER_size_t=size_t -c -fno-builtin -x c - -o gcc-builtins.o
rm gcc-builtins.o

echo "Successfully built gcc-builtins.h"
