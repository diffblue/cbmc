# Flag tests

Up until this point, the tests we have for the new SMT backend focus on getting
simple arithmetic or relational operator verification runs done.

This folder contains a couple of tests that are being run with CBMC flags, adding
extra assertions such as `--div-by-zero` or `--signed-overflow-check`.

Long term the plan is for this folder to be deleted, and the tests that are being
run as part of the old SMT backend (or maybe even the whole of CBMC's regression
test suite) to be run through a label or a flag. But for now, this should do well
enough to allow us to track the progress of our completion of the new backend.
