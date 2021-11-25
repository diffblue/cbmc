[CPROVER Manual TOC](../)

## Unsound CLI options for various tools

### Context

In [#6480](https://github.com/diffblue/cbmc/issues/6480), there has been some extensive
conversation about what it means for certain options to produce *unsound* behavior.

We concluded that *unsound* in this context is a proxy for the following two behaviors
that we want to avoid:

* **A spurious counter example to an assertion**, which means that the tool may report
  a coverage property (or a line of code) as reachable when in fact it is not, and
* **Wrong proof to an assertion**, which means that it might indicate an assertion passing
  when it's not.

We expect that, by default, CBMC and JBMC display none of the behavior we
described above (and if they do, it's an extremely serious bug that we aim to
fix on an ASAP basis), but be aware that certain tools, like `goto-instrument`,
may contain components that are experimental in nature and thus do
transformations that eventually lead to behavior such as the ones described
above. Furthermore, some options lead to unsound analysis results *by design*,
and some transformations performed by `goto-instrument` will yield verification
results that are (by design) unsound when taking verification of the
non-transformed program as reference.

### Examples of Options that may yield Unsound Results

The following options will produce a warning when used with CBMC or JBMC:

* Use of `--unwind` or `--unwindset` without `--unwinding-assertions`, or the
  use of `--partial-loops`.
* Depth or complexity-limited analysis (`--depth`, `--symex-complexity-limit`).

See [Understanding Loop Unwinding](../cbmc/unwinding/) for an elaboration of
these options.

### Experimental Options

Be advised that the following command line options to `cbmc` and `goto-instrument`
have been reported to be unsound:

* `--full-slice` has been reported to be unsound in issue [cbmc#260](https://github.com/diffblue/cbmc/issues/260)
  In particular, `--full-slice` appears to lead to spurious counter examples,
  because values that get assigned by a function whose body gets sliced out are
  no longer present in the trace, but still result in flipped verification results.

`cbmc` and `goto-instrument` have also been modified to warn that options used
are unsound as part of their output. An example of how that output looks is shown
below:

```sh
$ cbmc --full-slice ~/Devel/cbmc_bugs/6394/before-slice.out
CBMC version 5.45.0 (cbmc-5.43.0-77-g99c5a92de1-dirty) 64-bit arm64 macos
Reading GOTO program from file
Reading: ~/Devel/cbmc_bugs/6394/before-slice.out
Generating GOTO Program
Adding CPROVER library (x86_64)
Removal of function pointers and virtual functions
Generic Property Instrumentation
**** WARNING: Experimental option --full-slice, analysis results may be unsound. See https://github.com/diffblue/cbmc/issues/260
Performing a full slice
Running with 8 object bits, 56 offset bits (default)
Starting Bounded Model Checking
[...]
```
