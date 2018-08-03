\ingroup module_hidden 
\page other-tools Other Tools

\author Martin Brain, Peter Schrammel

# Other Tools

FIXME: The text in this section is a bit outdated.

The CPROVER subversion archive contains a number of separate programs.
Others are developed separately as patches or separate
branches.Interfaces are have been and are continuing to stablise but
older code may require work to compile and function correctly.

In the main archive:

* `CBMC`:   A bounded model checking tool for C and C++. See 
  \ref cbmc.

* `goto-cc`:   A drop-in, flag compatible replacement for GCC and other
  compilers that produces goto-programs rather than executable binaries.
  See \ref goto-cc.

* `goto-instrument`:   A collection of functions for instrumenting and
  modifying goto-programs. See \ref goto-instrument.

Model checkers and similar tools:

* `SatABS`:   A CEGAR model checker using predicate abstraction. Is
  roughly 10,000 lines of code (on top of the CPROVER code base) and is
  developed in its own subversion archive. It uses an external model
  checker to find potentially feasible paths. Key limitations are
  related to code with pointers and there is scope for significant
  improvement.

* `Scratch`:   Alistair Donaldson’s k-induction based tool. The
  front-end is in the old project CVS and some of the functionality is
  in `goto-instrument`.

* `Wolverine`:   An implementation of Ken McMillan’s IMPACT algorithm
  for sequential programs. In the old project CVS.

* `C-Impact`:   An implementation of Ken McMillan’s IMPACT algorithm for
  parallel programs. In the old project CVS.

* `LoopFrog`:   A loop summarisation tool.

* `TAN`:   Christoph’s termination analyser.

Test case generation:

* `cover`:   A basic test-input generation tool. In the old
    project CVS.

* `FShell`:   A test-input generation tool that allows the user to
  specify the desired coverage using a custom language (which includes
  regular expressions over paths). It uses incremental SAT and is thus
  faster than the naïve “add assertions one at a time and use the
  counter-examples” approach. Is developed in its own subversion.

Alternative front-ends and input translators:

* `Scoot`:   A System-C to C translator. Probably in the old
    project CVS.

* `???`:   A Simulink to C translator. In the old project CVS.

* `???`:   A Verilog front-end. In the old project CVS.

* `???`:   A converter from Codewarrior project files to Makefiles. In
    the old project CVS.

Other tools:

* `ai`:   Leo’s hybrid abstract interpretation / CEGAR tool.

* `DeltaCheck?`:   Ajitha’s slicing tool, aimed at locating changes and
  differential verification. In the old project CVS.

There are tools based on the CPROVER framework from other research
groups which are not listed here.
