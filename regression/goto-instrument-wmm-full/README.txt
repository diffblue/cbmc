REGRESSION TESTS FOR GOTO-INSTRUMENT --MM
-----------------------------------------

These regression tests are based on the results we obtained in 2012
for the paper ``Software Verification for Weak Memory via Program 
Transformation'', published in ESOP 2013.


(1) regression/goto-instrument-wmm and regression/goto-instrument-wmm-core
    ----------------------------------------------------------------------

regression/goto-instrument-wmm contains 4844 tests. It takes about 28' to
run all of them sequentially (make test) on dkr12 (Intel Xeon X5667, 8 cores 
at 3.07GHz, 48 GB of RAM). Testing for alpha-regressions only (make testalpha)
takes 27'.

regression/goto-instrument-wmm-core gathers 122 tests, selected for having
failed after limiting the cycle detection to two variables (unsound). The
whole test (make test) takes 42'' on dkr12. The alpha-regression tests
(make testalpha) take 39''. Improvement tests and new tests are not included
in this set of tests.


(2) tests for regressions w.r.t. soundness, precision and former results
    --------------------------------------------------------------------

REGRESSION TESTS: a difference indicates a regression
regression alpha: broke the soundness! -- C (core)
regression beta: lost some precision -- T (thorough)

IMPROVEMENT TESTS: a difference indicates an improvement
improvement: improved the precision -- K (known)

NEW TESTS: cannot be compared to previous results; new tests against the 
expected results. A difference indicates a bug.
new_tests: tests not supported in the previous experiments -- F (future)


for SC:

 old || new |
-------------------------------
 X   || OK  | regression alpha
 OK  || X   | regression beta


for WMM:

 old | exp || new |
-------------------------------------
 X   | X   || OK  | regression alpha
 X   | OK  || OK  | improvement
 OK  | X   || X   | impossible
 OK  | OK  || X   | regression beta
-------------------------------------
 ?   | OK  ||     | new_tests
 ?   | X   ||     | new_tests


In the tables above,
_old_ stands for the results obtained with goto-instrument --mm in 2012;
_new_ stands for the results obtained with the tested version;
_exp_ stands for the expected results, based on the original litmus tests
used to generate the C tests.


For each test in {regression_alpha, regression_beta, improvement}, report 
name : architecture : instrumentation strategy (if any) : old result.

For tests with ? in the previous results, these are not regression tests, but
new tests. In this case, report in new_tests
name : architecture : instrumentation strategy (if any) : expected result.


Note: for SC, if we have a ?, as no expected result is available, we skip.


(3) structure of the tests and parameters
    -------------------------------------

The Makefile calls test.pl with chain.sh, which runs the chain of tools needed
to verify the results of goto-instrument --mm.

goto-cc
goto-instrument --mm <arch> --<instrumentation-strategy>
cbmc

The paths of the three executables and their respective timeouts (180 sec each)
can be modified directly in chain.sh.


(4) construction of new regression tests (if needed in the future)
    --------------------------------------------------------------

Compile the parser reg.l and parse the last html results. Then execute
construction.sh with the four generated files as arguments, in order to set 
the new regression tests based on the previous results.
