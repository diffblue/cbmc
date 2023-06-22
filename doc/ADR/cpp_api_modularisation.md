\page cpp-api-and-modularisation Libcprover-cpp and Modularisation

**Date**: 22 Jun 2023
**Updated**: 22 Jun 2023
**Author**: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com
**Domain**: Architecture, API
**Description**: This document outlines our thinking about the rearchitecting of
    CBMC using the C++ API (`Libcprover-cpp`) as the central module and the
    transitioning of other tools to use that as a basis.

## Motivation && Current State of Affairs

CProver is a collection of tools fitting various program analysis needs. It
has been the product of the evolution of the codebase of the model-checking
tool for C (`CBMC`), after it has been adopted with various front-ends/back-ends
and various auxilliary tools.

During this time, the repository has grown organically, using some guidelines
for development that were based on tradition and intuition rather than some
tight development guide. This development model has been successful for most
of CProver's life, based on its nature as a hybrid industrial/academic and
experimental/applied tool. However, it has had the side-effect of accruing
some code duplication and technical debt. It has also made the codebase harder
to understand/develop and integrate with, especially for someone who is new
to the codebase.

The above concerns have generated discussions about the breaking down of
CProver into modules, with cleaner interfaces and tighter boundary control
between them, making the code easier to integrate in other projects (by making
the various component modules easier to combine and reuse) and making the
codebase easier to understand and maintain.

## The Plan Going Forward

Given the above outline, we have reached a point where we are strongly motivated
to take action to better componentise and modularise CProver.

It's also an opportune time for us, given the existence of `Libcprover-cpp`
the C++ API that we built to support interfacing with Rust (for now - other
languages may be coming in the future): we can use this as the basis of
development for an API exposing the interfaces of the various other modules
and refactor them into the better-defined shape we want them to take on
an incremental basis.

Of course, this is a project that is massive in scope, potentially being
exposed to further scope creep. We acknowledge that any effort to do what
we have discussed already is going to be a multi-year effort from our end,
and that we will need community alignment to achieve the outcome we're
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

This whole process has been very informational: we found out that not only
we *can* use the C++ API in that capacity, but also that extending the API
as and when we need to, and doing the various refactorings to the other tools
on a Just-In-Time basis is viable.

There have been, however, some limitations:

* The C++ API is still nascent, and as such its support for various workflows
  is just not present (at first). We can (and do) build things fast, as and
  when we need them - but it's nowhere near feature complete to provide for
  all of a user's workflows at the time of this writing.

* CProver tools have primarily been based on textual output to report on the
  results of their function (be it analysis, or transformations, etc). This
  hasn't been a problem up until this point (with the caveat that occassionally
  requests for support of new textual formats come up and adding support for
  those has become a laborious process).

  There's a need however for the separation of concerns between the production
  of the results by the analysis engine and the presentation layer for those.

We're working towards addressing these teething problems, but while we're
still operating on those, we have to accept some compromises in the architecture
of the code while we're iterating or stabilising several of the new or
refactored parts.

Be advised that some constructs may pop up in some limited locations
in the codebase that may appear questionable. We're only asking for
some patience while we're working out the best way to refactor them into
an architecture that is more cohesive with the long term vision for the
platform.

From our end, we will do our best to avoid any spillover effects to
other areas of the codebase, and to avoid introducing any behavioural
regressions while we're implementing the above plan.
