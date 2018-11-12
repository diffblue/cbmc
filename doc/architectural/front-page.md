CProver Developer Documentation
=====================

These pages contain user tutorials, automatically-generated API
documentation, and higher-level architectural overviews for the
CProver codebase. CProver is a platform for software verification.  Users can
download CProver tools from the <a href="http://www.cprover.org/">CProver
website</a>; contributors should use the
<a href="https://github.com/diffblue/cbmc">repository</a> hosted on GitHub. CBMC
is part of CProver.

CBMC is a Bounded Model Checker for C and C++ programs. It supports C89, C99,
most of C11 and most compiler extensions provided by gcc and Visual Studio. It
also supports SystemC using Scoot. It allows verifying array bounds (buffer
overflows), pointer safety, arithmetic exceptions and user-specified assertions.
Furthermore, it can check C and C++ for consistency with other languages, such
as Verilog. The verification is performed by unwinding the loops in the program
and passing the resulting equation to a decision procedure.

For further information see [cprover.org](http://www.cprover.org/cbmc).

Versions
========

Get the [latest release](https://github.com/diffblue/cbmc/releases)
* Releases are tested and for production use.

Get the current *develop* version: `git clone https://github.com/diffblue/cbmc.git`
* Develop versions are not recommended for production use.

Report bugs
===========

If you encounter a problem please file a bug report:
* Create an [issue](https://github.com/diffblue/cbmc/issues)

Contributing to the code base
=============================

1. Fork the the CBMC repository on GitHub.
2. Clone your fork with `git clone git@github.com:YOURNAME/cbmc.git`
3. Create a branch from the `develop` branch (default branch)
4. Make your changes - follow the
<a href="https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md">
coding guidelines</a>
5. Push your changes to your branch
6. Create a Pull Request targeting the `develop` branch

License
=======

<a href="https://github.com/diffblue/cbmc/blob/develop/LICENSE">4-clause BSD
license</a>.

Overview of Documentation
=======

### For users:

* The [CPROVER User Manual](http://www.cprover.org/cprover-manual/) details the
  capabilities of CBMC and describes how to install and use these tools. It
  also covers the underlying theory and prerequisite concepts behind how
  these tools work.

* There is a helpful user tutorial on the wiki with lots of linked resources,
you can access it <a href=
"https://svn.cprover.org/wiki/doku.php?id=cprover_tutorial">here</a>.

### For contributors:

The following pages attempt to provide the information that a developer needs to
work on CBMC, in a sensible order. In many cases they link to the appropriate
class-level or module-level documentation.

* \subpage compilation-and-development

* \subpage background-concepts

* \subpage cbmc-architecture

* \subpage folder-walkthrough

* \subpage code-walkthrough

* \subpage other-tools

* The \subpage tutorial "CBMC Developer Tutorial" helps new contributors
  to CProver to get their feet wet through a series of programming
  exercises - mostly modifying goto-instrument, and thus learning to
  manipulate the main data structures used within CBMC.

For higher-level architectural information, each of the pages under
the <a href="modules.html">Modules</a>
link gives an overview of a directory in the CProver codebase.

If you already know exactly what you're looking for, the best place
to look is the API reference, which
is generated from the codebase. You can search for classes and class
members in the search bar at top-right or use one of the links in the
sidebar.

\defgroup module_hidden _hidden
