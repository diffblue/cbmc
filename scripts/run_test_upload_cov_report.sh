#!/bin/bash

set -eou pipefail
FLAG=$1

if [[ "$FLAG" == "unit" ]]
then
  echo "Run $FLAG Tests"
  make -C unit test
  make -C jbmc/unit test
fi

if [[ "$FLAG" == "regression" ]]
then
  echo "Run $FLAG Tests"
  # Also enable compilation with coverage/profiling flags when running the
  # regression tests, to also get results for the driver program in
  # regression/invariants
  make -C regression test CPROVER_WITH_PROFILING=1
  make -C regression/cbmc test-paths-lifo
  make -C jbmc/regression test
fi

if [[ "$FLAG" == "cproversmt2" ]]
then
  echo "Run $FLAG Tests"
  env PATH=$PATH:`pwd`/src/solvers make -C regression/cbmc test-cprover-smt2
fi

lcov --capture --directory . --output-file lcov.info
lcov --remove lcov.info '/usr/*' '*/unit/*' --output-file lcov.info
# -f lcov.info is needed to avoid codecov.sh deleting gcno files including word 'coverage'. 
# -F is flag associate with the coverage report.
bash $COV_SCRIPT -t "$CODECOV_TOKEN" -f lcov.info -c -F $FLAG || true
# reset all execution counts to
lcov --zerocounters --directory .   
