CProver Documentation
=====================

\author Kareem Khazem

These pages contain user tutorials, automatically-generated API
documentation, and higher-level architectural overviews for the
CProver codebase. Users can download CProver tools from the
<a href="http://www.cprover.org/">CProver website</a>; contributors
should use the <a href="https://github.com/diffblue/cbmc">repository</a>
hosted on GitHub.

### For users:

* The \ref cprover-manual "CProver Manual" details the capabilities of
  CBMC and SATABS and describes how to install and use these tools. It
  also covers the underlying theory and prerequisite concepts behind how
  these tools work.

### For contributors:

* If you already know exactly what you're looking for, the API reference
  is generated from the codebase. You can search for classes and class
  members in the search bar at top-right or use one of the links in the
  sidebar.

* For higher-level architectural information, each of the pages under
  the "Modules" link in the sidebar gives an overview of a directory in
  the CProver codebase.

* The \ref module_cbmc "CBMC guided tour" is a good start for new
  contributors to CBMC. It describes the stages through which CBMC
  transforms source files into bug reports and counterexamples, linking
  to the relevant documentation for each stage.

* The \subpage cbmc-hacking "CBMC hacking HOWTO" helps new contributors
  to CProver to get their feet wet through a series of programming
  exercises---mostly modifying goto-instrument, and thus learning to
  manipulate the main data structures used within CBMC.

* The \subpage cbmc-guide "CBMC guide" is a single document describing
  the layout of the codebase and many of the important data structures.
  It probably contains more information than the module pages at the
  moment, but may be somewhat out-of-date.

\defgroup module_hidden _hidden
