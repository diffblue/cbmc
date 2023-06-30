\page cpp-api-and-modularisation libcprover-cpp and Modularisation

**Date**: 22 Jun 2023
**Updated**: 22 Jun 2023
**Author**: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com
**Domain**: Architecture, API
**Description**: This document outlines our thinking about the rearchitecting of
    CBMC using the C++ API (`libcprover-cpp`) as the central module and the
    transitioning of other tools to use that as a basis.

## Motivation && Current State of Affairs

CProver is a collection of tools fitting various program analysis needs. CProver
has been the product of the evolution of the codebase of the model-checking
tool for C (`CBMC`). Since then CProver has been adopted with various
front-ends/back-ends and auxilliary tools.

During this time, the repository has grown organically, using some guidelines
for development that were based on tradition and intuition rather than some
agreed architectural approach. This development model has been successful for most
of CProver's life, based on its nature as a hybrid industrial/academic and
experimental/applied tool. However, this has had the side-effect of accruing
some code duplication and technical debt. Consequently, the codebase is complex
and difficult to understand and develop for. This is a large barrier to new
developers, new features, and also improving and fixing the existing CProver
tools.

The above concerns have generated discussions about the breaking down of
CProver into modules, with cleaner interfaces and tighter boundary control
between them, making the code easier to integrate in other projects (by making
the various component modules easier to combine and reuse) and making the
codebase easier to understand and maintain.

The desire to separate functionality into different functional units
would also remove duplication and bloat, and prevent issues with the
same flag behaving in different ways across CProver tools.

## The Plan Going Forward

Given the above outline, we have reached a point where we are strongly motivated
to take action to better componentise and modularise CProver. What we mean by
"better componentise and modularise" is that right now, even though there
exists some structure between different CBMC components (at the class level
or at the code source file level), the different components aren't cleanly
separated in terms of boundaries/concerns, which hinders their reusability
or understandability.

It is also an opportune time for us, given the existence of `libcprover-cpp`
the C++ API that we built to support interfacing with Rust (for now - other
languages may be coming in the future): we can use this as the basis of
development for an API exposing the interfaces of the various other modules
and refactor them into the better-defined shape we want them to take on
an incremental basis.

Of course, this is a project that is massive in scope, potentially being
exposed to further scope creep. We acknowledge that any effort to do what
we have discussed already is going to be a multi-year effort from our end,
and that we will need community alignment to achieve the outcome we are
looking for.

This is why we are looking into testing the approach on a smaller component
first, to get a better feel for the amount of effort and any challenges
lurking in the dark.

## `goto-bmc` and `libcprover-cpp`

One of the objectives of our modularisation efforts is to decouple the
various components `CBMC` is based on (front-ends, backends, etc) to allow
for reuse/recombination. As a first segue into the larger effort, we wanted
a tool focusing only on running symex (the backend of our analysis engine)
on a GOTO-binary that has been preprocessed into an appropriate form.

We took the first steps for that in [cbmc#7762](https://github.com/diffblue/cbmc/pull/7762).

The aim of the PR was not only to allow for the tool with the narrower-scope
to come to life, but also to see if we could expose just enough of the
process to the C++ API and use that as the basis of the new tool.

This whole process has been very informative: we found out that not only
we *can* use the C++ API in that capacity, but also that extending the API
as and when we need to, and doing the various refactorings to the other tools
on a Just-In-Time basis is viable.

There have been, however, some limitations:

* The C++ API is still nascent, and as such its support for various workflows
  is just not present (yet). We can (and do) build things fast, as and
  when we need them - but it is nowhere near feature complete to provide for
  all of a user's workflows at the time of this writing.

* Still on the C++ API, its usage as the implementation basis for the new
  tool `goto-bmc` means that the code-structure and patterns in `goto-bmc`
  are going to differ from other existing tools in the CProver-suite.

* CProver tools have primarily been based on textual output to report on the
  results of their function (be it analysis, or transformations, etc). This
  has not been a problem up until this point (with the caveat that occasionally
  requests for support of new textual formats come up and adding support for
  those has become a laborious process).

  There is a need however for the separation of concerns between the production
  of the results by the analysis engine and the presentation layer for those.

We are working towards addressing these teething problems, but while we are
still operating on those, we have to accept some compromises in the architecture
of the code while we are iterating or stabilising several of the new or
refactored parts.

Be advised that some constructs may pop up in some limited locations
in the codebase that may appear questionable. We are only asking for
some patience while we are working out the best way to refactor them into
an architecture that is more cohesive with the long term vision for the
platform.

From our end, we will do our best to avoid any spillover effects to
other areas of the codebase, and to avoid introducing any behavioural
regressions while we are implementing the above plan. Any constructs
that may feature "questionable" changes to parts will be marked as such
and be followed with an explanation as to why the decision was made.
