#!/usr/bin/env bash

CC=$1
shift

for f in "$@"; do
    echo "Checking ${f}"
    cp "${f}" __libcheck.c
    perl -p -i -e 's/(__builtin_[^v])/s$1/' __libcheck.c
    perl -p -i -e 's/(_mm_.fence)/s$1/' __libcheck.c
    perl -p -i -e 's/(__sync_)/s$1/' __libcheck.c
    perl -p -i -e 's/(__atomic_)/s$1/' __libcheck.c
    "$CC" -std=gnu99 -E -include library/cprover.h -D__CPROVER_bool=_Bool -D__CPROVER_thread_local=__thread -DLIBRARY_CHECK -o __libcheck.i __libcheck.c
    "$CC" -S -Wall -Werror -pedantic -Wextra -std=gnu99 __libcheck.i \
      -o __libcheck.s -Wno-unused-label -Wno-unknown-pragmas
    ec="${?}"
    rm __libcheck.s __libcheck.i __libcheck.c
    [ "${ec}" -eq 0 ] || exit "${ec}"
done

# Make sure all internal library functions have tests exercising them:
grep '^/\* FUNCTION:' ../*/library/* | cut -f3 -d" " | sort -u > __functions

# Some functions are not expected to have tests:
perl -p -i -e 's/^__CPROVER_jsa_synthesise\n//' __functions
perl -p -i -e 's/^java::java.io.InputStream.read:\(\)I\n//' __functions

# Some functions are implicitly covered by running on different operating
# systems:
perl -p -i -e 's/^_fopen\n//' __functions # fopen, macOS
perl -p -i -e 's/^_pipe\n//' __functions # pipe, macOS
perl -p -i -e 's/^_time32\n//' __functions # time, Windows
perl -p -i -e 's/^_time64\n//' __functions # time, Windows

# Some functions are covered by existing tests:
perl -p -i -e 's/^__builtin_alloca\n//' __functions # alloca-01
perl -p -i -e 's/^__builtin_clzl\n//' __functions # __builtin_clz-01
perl -p -i -e 's/^__builtin_clzll\n//' __functions # __builtin_clz-01
perl -p -i -e 's/^__builtin_ffsl\n//' __functions # __builtin_ffs-01
perl -p -i -e 's/^__builtin_ffsll\n//' __functions # __builtin_ffs-01
perl -p -i -e 's/^__lzcnt\n//' __functions # __builtin_clz-01
perl -p -i -e 's/^__lzcnt16\n//' __functions # __builtin_clz-01
perl -p -i -e 's/^__lzcnt64\n//' __functions # __builtin_clz-01
perl -p -i -e 's/^fclose_cleanup\n//' __functions # fopen

# Some functions are covered by tests in other folders:
perl -p -i -e 's/^__builtin_sadd_overflow\n//' __functions # cbmc/gcc_builtin_add_overflow
perl -p -i -e 's/^__builtin_saddl_overflow\n//' __functions # cbmc/gcc_builtin_add_overflow
perl -p -i -e 's/^__builtin_saddll_overflow\n//' __functions # cbmc/gcc_builtin_add_overflow
perl -p -i -e 's/^__builtin_smul_overflow\n//' __functions # cbmc/gcc_builtin_mul_overflow
perl -p -i -e 's/^__builtin_smull_overflow\n//' __functions # cbmc/gcc_builtin_mul_overflow
perl -p -i -e 's/^__builtin_smulll_overflow\n//' __functions # cbmc/gcc_builtin_mul_overflow
perl -p -i -e 's/^__builtin_ssub_overflow\n//' __functions # cbmc/gcc_builtin_sub_overflow
perl -p -i -e 's/^__builtin_ssubl_overflow\n//' __functions # cbmc/gcc_builtin_sub_overflow
perl -p -i -e 's/^__builtin_ssubll_overflow\n//' __functions # cbmc/gcc_builtin_sub_overflow
perl -p -i -e 's/^__builtin_uadd_overflow\n//' __functions # cbmc/gcc_builtin_add_overflow
perl -p -i -e 's/^__builtin_uaddl_overflow\n//' __functions # cbmc/gcc_builtin_add_overflow
perl -p -i -e 's/^__builtin_uaddll_overflow\n//' __functions # cbmc/gcc_builtin_add_overflow
perl -p -i -e 's/^__builtin_umul_overflow\n//' __functions # cbmc/gcc_builtin_mul_overflow
perl -p -i -e 's/^__builtin_umull_overflow\n//' __functions # cbmc/gcc_builtin_mul_overflow
perl -p -i -e 's/^__builtin_umulll_overflow\n//' __functions # cbmc/gcc_builtin_mul_overflow
perl -p -i -e 's/^__builtin_usub_overflow\n//' __functions # cbmc/gcc_builtin_sub_overflow
perl -p -i -e 's/^__builtin_usubl_overflow\n//' __functions # cbmc/gcc_builtin_sub_overflow
perl -p -i -e 's/^__builtin_usubll_overflow\n//' __functions # cbmc/gcc_builtin_sub_overflow
perl -p -i -e 's/^__builtin_ia32_vec_ext_v16qi\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_ext_v2di\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_ext_v4sf\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_ext_v4si\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_extract_epi32\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_set_epi32\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_setr_epi32\n//' __functions # cbmc/SIMD1

ls ../../regression/cbmc-library/ | grep -- - | cut -f1 -d- | sort -u > __tests
diff -u __tests __functions
ec="${?}"
rm __functions __tests
exit "${ec}"
