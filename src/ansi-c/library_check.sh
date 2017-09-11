#!/bin/bash

# Note use of -Wno-nonnull-compare below: functions in string.c (and others) null-check their parameters,
# but some versions of libc tag them non-null, authorising the optimiser to discard those checks.
# This is acceptable to use because this version of the library is only for use by cbmc, which does
# not use the non-null attribute in this way.
# See https://clang.llvm.org/docs/AttributeReference.html#nonnull-gnu-nonnull

if echo "" | "$CC" -Werror -Wno-nonnull-compare -E - >/dev/null 2>&1; then
  # Expected option for gcc
  DISABLE_NONNULL_WARNING=-Wno-nonnull-compare
elif echo "" | "$CC" -Werror -Wno-tautological-pointer-compare -Wno-pointer-bool-conversion -E - >/dev/null 2>&1; then
  # Expected option for clang
  DISABLE_NONNULL_WARNING="-Wno-tautological-pointer-compare -Wno-pointer-bool-conversion"
else
  echo >&2 "Couldn't find compiler options to disable warnings regarding comparison vs. __nonnull__ pointers, this may cause test failures"
fi

for f in "$@"; do
	echo "Checking $f"
	cp $f __libcheck.c
	perl -p -i -e 's/(__builtin_[^v])/s$1/' __libcheck.c
	perl -p -i -e 's/(__sync_)/s$1/' __libcheck.c
	perl -p -i -e 's/(__noop)/s$1/' __libcheck.c
	"$CC" -std=gnu99 -E -include library/cprover.h -D__CPROVER_bool=_Bool -D__CPROVER_thread_local=__thread -DLIBRARY_CHECK -o __libcheck.i __libcheck.c
	"$CC" -S -Wall -Werror -pedantic -Wextra $DISABLE_NONNULL_WARNING -std=gnu99 __libcheck.i -o __libcheck.s -Wno-unused-label
	ec=$?
	$RM __libcheck.s __libcheck.i __libcheck.c
	[ $ec -eq 0 ] || exit $ec
done
