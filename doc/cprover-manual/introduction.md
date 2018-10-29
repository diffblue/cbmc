# Introduction

## Motivation

Numerous tools to hunt down functional design flaws in silicon have been
available for many years, mainly due to the enormous cost of hardware
bugs. The use of such tools is wide-spread. In contrast, the market for
tools that address the need for quality software is still in its
infancy.

Research in software quality has an enormous breadth. We focus the
presentation using two criteria:

1.  We believe that any form of quality requires a specific *guarantee*,
    in theory and practice.
2.  The sheer size of software designs requires techniques that are
    highly *automated*.

In practice, quality guarantees usually do not refer to "total
correctness" of a design, as ensuring the absence of all bugs is too
expensive for most applications. In contrast, a guarantee of the absence
of specific flaws is achievable, and is a good metric of quality.

## Bounded Model Checking with CBMC

CBMC implements a technique called *Bounded Model Checking* (BMC). In
BMC, the transition relation for a complex state machine and its
specification are jointly unwound to obtain a Boolean formula, which is
then checked for satisfiability by using an efficient SAT procedure. If
the formula is satisfiable, a counterexample is extracted from the
output of the SAT procedure. If the formula is not satisfiable, the
program can be unwound more to determine if a longer counterexample
exists.

In many engineering domains, real-time guarantees are a strict
requirement. An example is software embedded in automotive controllers.
As a consequence, the loop constructs in these types of programs often
have a strict bound on the number of iterations. CBMC is able to
formally verify such bounds by means of *unwinding assertions*. Once
this bound is established, CBMC is able to prove the absence of errors.

A more detailed description of how to apply CBMC to verify programs is
in the [CBMC Tutorial](../cbmc/tutorial/).
