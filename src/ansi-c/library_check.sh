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
    $CC -std=gnu11 -E -include library/cprover.h -D__CPROVER_bool=_Bool -D__CPROVER_thread_local=__thread -DLIBRARY_CHECK -o __libcheck.i __libcheck.c
    $CC -S -Wall -Werror -pedantic -Wextra -std=gnu11 __libcheck.i \
      -o __libcheck.s -Wno-unused-label -Wno-unknown-pragmas \
      -Wno-dollar-in-identifier-extension \
      -Wno-gnu-line-marker -Wno-unknown-warning-option -Wno-psabi
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
perl -p -i -e 's/^_creat\n//' __functions # creat, macOS
perl -p -i -e 's/^_fcntl\n//' __functions # fcntl, macOS
perl -p -i -e 's/^_fopen\n//' __functions # fopen, macOS
perl -p -i -e 's/^_getopt\n//' __functions # getopt, macOS
perl -p -i -e 's/^_mmap\n//' __functions # mmap, macOS
perl -p -i -e 's/^_munmap\n//' __functions # mumap, macOS
perl -p -i -e 's/^_open\n//' __functions # open, macOS
perl -p -i -e 's/^_openat\n//' __functions # openat, macOS
perl -p -i -e 's/^_pipe\n//' __functions # pipe, macOS
perl -p -i -e 's/^_setjmp\n//' __functions # pipe, macOS
perl -p -i -e 's/^_time(32|64)\n//' __functions # time, Windows
perl -p -i -e 's/^__builtin___snprintf_chk\n//' __functions # snprintf, macOS
perl -p -i -e 's/^__builtin___vsnprintf_chk\n//' __functions # vsnprintf, macOS
perl -p -i -e 's/^__fcntl_time64\n//' __functions # fcntl, Linux
perl -p -i -e 's/^__inet_(addr|aton|ntoa|network)\n//' __functions # inet_*, FreeBSD
perl -p -i -e 's/^__isoc99_v?fscanf\n//' __functions # fscanf, Linux
perl -p -i -e 's/^__isoc99_v?scanf\n//' __functions # scanf, Linux
perl -p -i -e 's/^__isoc99_v?sscanf\n//' __functions # sscanf, Linux
perl -p -i -e 's/^__sigsetjmp\n//' __functions # sigsetjmp, Linux
perl -p -i -e 's/^__stdio_common_vfscanf\n//' __functions # fscanf, Windows
perl -p -i -e 's/^__stdio_common_vsprintf\n//' __functions # snprintf, Windows
perl -p -i -e 's/^__stdio_common_vsscanf\n//' __functions # sscanf, Windows
perl -p -i -e 's/^__srget\n//' __functions # gets, FreeBSD
perl -p -i -e 's/^__swbuf\n//' __functions # putc, FreeBSD
perl -p -i -e 's/^__tolower\n//' __functions # tolower, macOS
perl -p -i -e 's/^__toupper\n//' __functions # toupper, macOS

# Some functions are covered by existing tests:
perl -p -i -e 's/^__CPROVER_(creat|fcntl|open|openat)\n//' __functions # creat, fcntl, open, openat
perl -p -i -e 's/^__CPROVER_(tolower|toupper)\n//' __functions # tolower, toupper
perl -p -i -e 's/^(creat|fcntl|open|openat)64\n//' __functions # same as creat, fcntl, open, openat
perl -p -i -e 's/^__CPROVER_deallocate\n//' __functions # free-01
perl -p -i -e 's/^__builtin_alloca\n//' __functions # alloca-01
perl -p -i -e 's/^fclose_cleanup\n//' __functions # fopen
perl -p -i -e 's/^fopen64\n//' __functions # fopen
perl -p -i -e 's/^freopen64\n//' __functions # freopen
perl -p -i -e 's/^mmap64\n//' __functions # mmap
perl -p -i -e 's/^munmap\n//' __functions # mmap-01
perl -p -i -e 's/^__fgets_chk\n//' __functions # fgets-01/__fgets_chk.desc
perl -p -i -e 's/^__fprintf_chk\n//' __functions # fprintf-01/__fprintf_chk.desc
perl -p -i -e 's/^__fread_chk\n//' __functions # fread-01/__fread_chk.desc
perl -p -i -e 's/^__printf_chk\n//' __functions # printf-01/__printf_chk.desc
perl -p -i -e 's/^__syslog_chk\n//' __functions # syslog-01/__syslog_chk.desc
perl -p -i -e 's/^_syslog\$DARWIN_EXTSN\n//' __functions # syslog-01/test.desc
perl -p -i -e 's/^__time64\n//' __functions # time
perl -p -i -e 's/^__vfprintf_chk\n//' __functions # vfprintf-01/__vfprintf_chk.desc

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
