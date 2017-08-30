#!/usr/bin/env bash

for var in "$@"; do
    cp "${var}" __libcheck.c
    sed -i 's/__builtin_[^v]/s&/' __libcheck.c
    sed -i 's/__sync_/s&/' __libcheck.c
    sed -i 's/__noop/s&/' __libcheck.c
    cc -std=gnu99 -E -include library/cprover.h -D__CPROVER_bool=_Bool -D__CPROVER_thread_local=__thread -DLIBRARY_CHECK -o __libcheck.i __libcheck.c
    cc -S -Wall -Werror -pedantic -Wextra -std=gnu99 __libcheck.i -o __libcheck.s -Wno-unused-label -Wno-uninitialized

    ec="$?"
    rm __libcheck.s __libcheck.i __libcheck.c
    [ "${ec}" -eq 0 ] || exit "${ec}"
done
