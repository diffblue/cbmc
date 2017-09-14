#!/usr/bin/env bash

for f in "$@"; do
    echo "Checking ${f}"
    cp "${f}" __libcheck.c
    perl -p -i -e 's/(__builtin_[^v])/s$1/' __libcheck.c
    perl -p -i -e 's/(__sync_)/s$1/' __libcheck.c
    perl -p -i -e 's/(__noop)/s$1/' __libcheck.c
    cc -std=gnu99 -E -include library/cprover.h -D__CPROVER_bool=_Bool -D__CPROVER_thread_local=__thread -DLIBRARY_CHECK -o __libcheck.i __libcheck.c
    cc -S -Wall -Werror -pedantic -Wextra -std=gnu99 __libcheck.i -o __libcheck.s -Wno-unused-label
    ec="${?}"
    rm __libcheck.s __libcheck.i __libcheck.c
    [ "${ec}" -eq 0 ] || exit "${ec}"
done
