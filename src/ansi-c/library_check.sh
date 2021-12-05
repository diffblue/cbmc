#!/usr/bin/env bash

CC=$1
shift

for f in "$@"; do
    echo "Checking ${f}"
    cp "${f}" __libcheck.c
    perl -p -i -e 's/(__builtin_[^v])/s$1/' __libcheck.c
    perl -p -i -e 's/s(__builtin_unreachable)/$1/' __libcheck.c
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
