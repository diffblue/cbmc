# Documentation

[CBMC](https://github.com/diffblue/cbmc) is a model checker for
C. This means that CBMC will explore all possible paths through your
code on all possible inputs, and will check that all assertions in
your code are true. CBMC can also check for the possibility of memory
safety errors (like buffer overflow) and for instances of undefined
behavior (like signed integer overflow). CBMC is a *bounded* model
checker, however, and using CBMC may require restricting inputs to
inputs of some bounded size. The result is assurance that your code
behaves as expected for all such inputs.

This page is the root of all documentation for CBMC:

* The \subpage installation_guide describes how to install CBMC
* The \subpage user_guide describes what you need to know to use CBMC
* The \subpage reference_guide describes the CBMC tools
* The \subpage developer_guide describes what you need to know to contribute
  to CBMC

CBMC documentation has traditionally been generated from
doxygen comments in the source code and a few additional markdown files.
Over time, we will move this documentation into the guides listed above,
but for now, this source code documentation is avilable here:

* \subpage cprover_documentation

CBMC documentation will never be done.  If you learn something interesting
or find a mistake, please consider contributing documentation with a
[pull request](https://github.com/diffblue/cbmc/pulls)
or describing the problem to us by filing an
[issue](https://github.com/diffblue/cbmc/issues).
Some advice on contributing documentation is available here:

* \subpage contributing_documentation
