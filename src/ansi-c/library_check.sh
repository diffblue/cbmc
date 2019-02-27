#!/usr/bin/env bash

CC=$1
shift

for f in "$@"; do
    echo "Checking ${f}"
    cp "${f}" __libcheck.c
    perl -p -i -e 's/(__builtin_[^v])/s$1/' __libcheck.c
    perl -p -i -e 's/s(__builtin_unreachable)/$1/' __libcheck.c
    perl -p -i -e 's/s(__builtin_(add|mul)_overflow)/$1/' __libcheck.c
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
perl -p -i -e 's/^__CPROVER_contracts_library\n//' __functions

# Some functions are implicitly covered by running on different operating
# systems:
perl -p -i -e 's/^_fopen\n//' __functions # fopen, macOS
perl -p -i -e 's/^_mmap\n//' __functions # mmap, macOS
perl -p -i -e 's/^_munmap\n//' __functions # mumap, macOS
perl -p -i -e 's/^_pipe\n//' __functions # pipe, macOS
perl -p -i -e 's/^_setjmp\n//' __functions # pipe, macOS
perl -p -i -e 's/^_time(32|64)\n//' __functions # time, Windows
perl -p -i -e 's/^__isoc99_v?fscanf\n//' __functions # fscanf, Linux
perl -p -i -e 's/^__isoc99_v?scanf\n//' __functions # scanf, Linux
perl -p -i -e 's/^__isoc99_v?sscanf\n//' __functions # sscanf, Linux
perl -p -i -e 's/^__sigsetjmp\n//' __functions # sigsetjmp, Linux
perl -p -i -e 's/^__stdio_common_vfscanf\n//' __functions # fscanf, Windows
perl -p -i -e 's/^__stdio_common_vsscanf\n//' __functions # sscanf, Windows

# Some functions are covered by existing tests:
perl -p -i -e 's/^__CPROVER_deallocate\n//' __functions # free-01
perl -p -i -e 's/^__builtin_alloca\n//' __functions # alloca-01
perl -p -i -e 's/^fclose_cleanup\n//' __functions # fopen
perl -p -i -e 's/^munmap\n//' __functions # mmap-01

# Some functions are covered by tests in other folders:
perl -p -i -e 's/^__spawned_thread\n//' __functions # any pthread_create tests
perl -p -i -e 's/^__builtin_ffsl?l?\n//' __functions # cbmc/__builtin_ffs-01
perl -p -i -e 's/^__builtin_[su]addl?l?_overflow\n//' __functions # cbmc/gcc_builtin_add_overflow
perl -p -i -e 's/^__builtin_[su]mull?l?_overflow\n//' __functions # cbmc/gcc_builtin_mul_overflow
perl -p -i -e 's/^__builtin_[su]subl?l?_overflow\n//' __functions # cbmc/gcc_builtin_sub_overflow
perl -p -i -e 's/^__builtin_ia32_p(add|sub)sw\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_psubu?sw128\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_ext_v16qi\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_ext_v2di\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_ext_v4s[fi]\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_ext_v[48]hi\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^__builtin_ia32_vec_init_v4hi\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_adds_ep[iu]16\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_extract_epi(16|32)\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_extract_pi16\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_set_epi(16|32)\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_set_pi16\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_setr_epi(16|32)\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_setr_pi16\n//' __functions # cbmc/SIMD1
perl -p -i -e 's/^_mm_subs_ep[iu]16\n//' __functions # cbmc/SIMD1

ls ../../regression/cbmc-library/ | grep -- - | cut -f1 -d- | sort -u > __tests
diff -u __tests __functions
ec="${?}"
rm __functions __tests
if [ $ec != 0 ]; then
  echo "Tests and library functions don't match."
  echo "Lines prefixed with - are tests not matching any library function."
  echo "Lines prefixed with + are functions lacking a test."
fi
exit "${ec}"
