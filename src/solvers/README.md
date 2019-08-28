\ingroup module_hidden
\defgroup solvers solvers
# Folder solvers

\authors Romain Brenguier, Kareem Khazem, Martin Brain

\section solvers-overview Overview

This directory contains most of the decision procedure code in CPROVER.
A decision procedure is an algorithm which can check if a set of logical
statements is satisfiable, i.e. if there is a value for each variable which
makes all of them true at the same time.  Formally all
that is needed is determining if they are satisfiable, in practice it
is often very valuable to know the assignments of the variables.
Tools (and components) that implement decision procedures are often
called solvers.  For example a SAT solver is a tool that implements a
decision procedure for checking the satisfiability of formulae (often
in CNF) over Boolean variables.  An SMT solver is a tool that
implements decision procedures for the Satisfiability Modulo Theories
class of problems.  CPROVER includes its own SMT solver, built on top
of a SAT solver but can also interface to external solvers.

CBMC and JBMC create formulae which describe some of the execution of parts of a
program (see \ref goto-symex for how this is done) and then use a solver to see
if there are any executions which break an assertion.  If the formula describing
the execution and the formula describing the assertion are satisfiable
then it is possible for the assertion to fail and the assignment of the
variables can be used to build an error trace (see \ref goto_tracet).  Thus
the performance and capability of the solver used is crucial to the utility of
CBMC and JBMC.  Other tools make use of solvers in other ways to handle other
problems.  It is important to distinguish between goto-models,
goto-programs, etc. which describe programs and have a semantics in
terms of execution and formula that have a semantics in terms of
logic.  Solvers work with formulae and so have no notion of execution
order, assignment, "before", branching, loops, exceptions,
side-effects, function calls, etc.  All of these have to be described
in the formula presented to the decision procedure if you want to reason about them.

Other tools use solvers in different ways but the basic interface and
ideas remain the same.


\section solvers-interfaces Key Interfaces

The most basic interface is `decision_proceduret`.  It gives the
interface of all decision procedures.  You call `set_to_true` and
`set_to_false` to give the formulae and then `dec_solve` to check if
they are satisfiable.  If they are, it returns `D_SATISFIABLE` and you
can use `get` to find the values in the satisfying assignment (if the
underlying decision procedure supports this).  If you are implementing
a solver, then this is the most basic interface you have to support,
if you are using the solver, this is the best interface to use as it
does not commit you to any particular kind of solver.  Looking at the
inheritance diagram from `decision_proceduret` is a good way of
getting an over-view of the solvers currently supported.

Many (but not all) decision procedures have a notion of logical
expression and can provide information about logical expressions
within the solver.  `prop_convt` expands on the interface of
`decision_proceduret` to add a data-type (`literalt`) and interfaces
for manipulating logical expressions within the solver.

Within decision procedures it is common to reduce the logical
expressions to equivalent expressions in a simpler language.  This is
similar to what a compiler will do in reducing higher-level language
constructs to simple, assembler like instructions.  This, of course,
relies on having a decision procedure for the simpler language, just
as a compiler relies on you having a processor that can handle the
assembler.  One of the popular choices of "processor" for decision
procedures are SAT solvers.  These handle a very restricted language
in which all variables are simple Booleans and all formulae are just
made of logical gates.  By keeping their input simple, they can be
made very fast and efficient; kind of like RISC processors.  Like
processors, creating a good SAT solver is a very specialised skill, so
CPROVER uses third-party SAT solvers.  By default this is MiniSAT, but
others are supported (see the `sat/` directory).  To do this it needs a
software interface to a SAT solver : this is `propt`.  It uses the
same `literalt` to refer to Boolean variables, just as `prop_convt`
uses them to refer to logical expressions.  `land`, `lor`, `lxor` and
so on allow gates to be constructed to express the formulae to be
solved.  If `cnf_handled_well` is true then you may also use `lcnf` to
build formulae.  Finally, `prop_solve` will run the decision procedure.

As previously mentioned, many decision procedures reduce formulae to
CNF and solve with a SAT solver.  `prop_conv_solvert` contains the
foundations of this conversion.  It implements the `prop_convt` by
having an instance of `propt` (a SAT solver) and reducing the
expressions that are input into CNF.  The key entry point to this
procedure is `prop_conv_solvert::convert` which then splits into
`prop_conv_solvert::convert_boolean` (which
uses `propt::land` and so on to convert Boolean expressions) and
`prop_conv_solvert::convert_rest` which gives an error to start with.
Various solvers inherit from `prop_conv_solvert` adding to `convert` and
`convert_rest` to increase the language of expressions that can be
converted.  `equalityt` adds handling of equality between variables,
`arrayst` then builds on that to add support for arrays, `boolbvt`
adds bit-vector operations (plus, negate, multiply, shift, etc.) and
finally `bv_pointers` adds pointers.  This layering simplifies the
conversion to CNF and allows parts of it to be over-ridden and
modified (as `bv_refinementt` and `string_refinementt` do).


\section solvers-directories Directories

* `prop/`:   The interfaces above mostly live in `prop/`, which also
  contains a number of other supporting classes, like `literal.h`.

* `sat/`:   All of the code for interacting and interfacing with SAT
  solvers.  This is largely a 'leaf' directory and makes little use of
  external interfaces beyond things in `prop`.  `cnf.h` contains
  `cnft` and `cnf_solvert` which give default implements `propt`s gate
  functions (`land`, `lxor`, etc.) in terms of `lcnf` as most modern
  SAT solvers only have interfaces for handling CNF, not logical
  gates.  The various satcheck_* files implement the `propt`
  interfaces (generally with the `cnf_solvert` additions /
  simplifications) by connecting to various third-party SAT solvers.
  Finally `satcheck.h` use the build time flags to pick which SAT
  solvers are available and which should be used as default.

* `qbf/`:   An equivalent of `sat/` for QBF solvers.  These extend
 the basic language of SAT solvers with universal and existential
 quantification over Boolean variables.  This makes the solvers more
 expressive but also slower.  `qbf/` is not used by the main CPROVER
 tools and the solvers it integrates are somewhat dated.

* `flattening/`:   A library that converts operations to bit-vectors,
  including calling the conversions in `floatbv` as necessary. Is
  implemented as a simple conversion (with caching) and then a
  post-processing function that adds extra constraints.  The `boolbvt`
  solver uses these to express bit-vector operations via the `propt`
  interfaces. This is not used by the SMT2 back-ends.

* smt2/:   Provides the `smt2_dect` type which converts the formulae to
  SMT-LIB 2 and then invokes one of Boolector, CVC3, CVC4, MathSAT, Yices or Z3.
  Note that the interaction with the solver is batched and uses
  temporary files rather than using the interactive command supported by
  SMT-LIB 2. With the `–fpa` option, this output mode will not flatten
  the floating point arithmetic and instead output SMT-LIB floating point standard.

* `floatbv/`:    This library contains the code that is used to
  convert floating point variables (`floatbv`) to bit vectors
  (`bv`). This is referred to as ‘bit-blasting’ and is called in the
  `solver` code during conversion to SAT or SMT. It also contains the
  abstraction code described in the FMCAD09 paper.

* `lowering/`:  These are `exprt` to `exprt` reductions of operations
   rather than the `exprt` to `bvt` reductions in `flattening/`
   allowing them to be used in SMT solvers which do not inherit from
   `prop_conv_solvert`.

* `refinement/`: Solvers that build on the `bv_pointerst` solver
   interface and specialise the handling of certain operations to
   improve performance.

* `miniBDD/`:  A canonical representation of Boolean formulae.




\section flattening-section Flattening

**Key classes:**
* \ref propt (in solvers/prop)
* \ref boolbvt
* \ref bv_utilst

The main class in this folder is \ref boolbvt which wraps a variety of 
helper methods and classes (including inherited ones) and acts as an interface 
for transforming \ref exprt into boolean formula and then solving it.

Many of its methods are focused around transforming a particular \ref exprt 
into a vector of \ref literalt and then passing them to a \ref propt 
for formula building / solving.

The primary methods are:

Note: `bvt` mentioned below is an alias to a vector of literalt.

`bvt boolbvt::convert_bitvector(const exprt &expr)`

Which takes an exprt then calls the associated transformation functions to
generate the \ref literalt vector to then pass to the internal \ref propt instance.

`const bvt & boolbvt::convert_bv(const exprt &expr, optionalt<std::size_t> expected_width)`

Similar to convert_bitvector except it also provides basic caching and
freezing results for incremental solving. It calls convert_bitvector
internally.

`literalt boolbvt::convert_rest(const exprt &expr)`

(Note: I'm not sure why this is split from the normal convert_bitvector, 
but it's probably worth mentioning)

`void post_process()`

Performs any post-processing, which is normally adding constraints that 
require some global knowledge of the formula, ex. for encoding arrays 
into uninterpreted functions.

**Some key classes:**

\ref propt is instance of whichever solver is currently being used. This
inherits from `decision_proceduret` whose interface has a fuller explanation 
in the "General Interfaces" subsection.

\ref bv_utilst holds a set of utility functions for bit manipulation that work
upon [literal](\ref literalt)s (or vectors of them). Holds a reference to the propt 
that its parent uses.

\ref functionst Helper class that keeps a list of uninterpreted functions
which then gets used to add function constraints when `post_process` is called.

\ref boolbv_mapt Helper class that maps an \ref irep_idt (and a type) to a 
vector of [literal](\ref literalt)s. 

\ref arrayst Base class of \ref boolbvt. Adds additional array constraints 
when `post_process` is called.

\ref equalityt Base class of \ref boolbvt. Adds equality constraints between
bitvectors when `post_process` is called.

\section solver-apis Solver APIs

\subsection smt-solving-api-section SMT solving API

To be documented.

\subsection sat-solving-api-section SAT solving API

The basic SAT solver interface is in [cnf](\ref cnft). This inherits
from the [propositional logic decision procedure wrapper](\ref propt).

The interface supports the following operations by default:
1. Boolean operations on literals (like `and`, `or`, `xor`), etc.
These take as input two [literals](\ref literalt) and return as
output another [literal](\ref literalt), applying Tseitin's
transformation on them. Tseitin's transformation converts a
propositional formula `F` into an equisatisfiable CNF formula
that is linear in the size of `F`. For more information look at:
https://en.wikipedia.org/wiki/Tseytin_transformation
2. Generating new [literals](\ref literalt) and adding their
variables to the formula and returning the number of variables
or clauses the solver is operating with (with `no_variables`).

This interface is then extended by the various solver interfaces
which implement the interface by hooking into the solver
related functions that implement the operations that they
abstract. Solvers for which drivers exist include Minisat,
Minisat2, Chaff, Picosat, Glucose, Cadical, Booleforce and Lingeling.

For example, the Minisat 2 interface (in `satcheck_minisat2.h`)
implements a method `prop_solve()` that hooks into Minisat 2's
interface by initialising the variable list Minisat 2 will use,
and then invoking the actual solver on the formula and checking
whether the solver could manage find a satisfying assignment or
not.

For more details on how the particular drivers work, refer
to them in their interface and implementation files, which follow
the naming pattern `satcheck_x`, where `x` is the name of the
solver.

We also support any solver that can hook into [ipasir](http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/IPASIR____IPASIR). This is a
generic incremental SAT solver API. This is handled by the
`satcheck_ipasir.h` interface abstracts over `ipasir` with our own
generic interface. For a description of the `ipasir` interface
take a look at the following file: [ipasir.h](https://github.com/biotomas/ipasir/blob/master/ipasir.h)

\section sat-smt-encoding SAT/SMT Encoding

In the \ref solvers directory.

**Key classes:**
* \ref literalt
* \ref boolbvt
* \ref propt

\dot
digraph G {
	node [shape=box];
	rankdir="LR";
	1 [shape=none, label=""];
	2 [label="goto conversion"];
	3 [shape=none, label=""];
	1 -> 2 [label="equations"];
	2 -> 3 [label="propositional variables as bitvectors, constraints"];
}
\enddot

---

\section decision-procedure Decision Procedure

In the \ref solvers directory.

**Key classes:**
* symex_target_equationt
* \ref propt

\dot
digraph G {
	node [shape=box];
	rankdir="LR";
	1 [shape=none, label=""];
	2 [label="goto conversion"];
	3 [shape=none, label=""];
	1 -> 2 [label="propositional variables as bitvectors, constraints"];
	2 -> 3 [label="solutions"];
}
\enddot

\section string-solver-interface String Solver Interface

The string solver is particularly aimed at string logic, but since it inherits
from \ref bv_refinementt it is also capable of handling arithmetic, array logic,
floating point operations etc.
The backend uses the flattening of \ref boolbvt to convert expressions to boolean formula.

An example of a problem given to string solver could look like this:

~~~~~
return_code == cprover_string_concat_func(
  length1, array1,
  { .length=length2, .content=content2 },
  { .length=length3, .content=content3 })
length3 == length2
content3 == content2
is_equal == cprover_string_equals_func(length1, array1, 2, {'a', 'a'})
is_equal == 1
~~~~~

Details about the meaning of the primitives `cprover_string_concat_func` and
`cprover_string_equals_func` are given in section \ref primitives "String Primitives".

The first equality means that the string represented by `{length1, array1}` is
the concatanation of the string represented by `{length2, array2}` and
`{length3, array3}`. The second and third mean that `{length2, array2}` and
`{length3, array3}` represent the same string. The fourth means that `is_equal`
is 1 if and only if `{length1, array1}` is the string "aa". The last equation
ensures that `is_equal` has to be equal to 1 in the solution.

For this system of equations the string solver should answer that it is
satisfiable. It is then possible to recover which assignments make all
equation true, in that case `length2 = length3 = 1` and
`content2 = content3 = {'a'}`.


\subsection general_interface General interface

The common interface for solvers in CProver is inherited from
`decision_proceduret` and is the common interface for all solvers.
It is essentially composed of these three functions:

  - `string_refinementt::set_to(const exprt &expr, bool value)`:
  \copybrief string_refinementt::set_to
  - `string_refinementt::dec_solve()`:
  \copybrief string_refinementt::dec_solve
  - `string_refinementt::get(const exprt &expr) const`:
  \copybrief string_refinementt::get

For each goal given to CProver:
  - `set_to` is called on several equations, roughly one for each step of the
    symbolic execution that leads to that goal;
  - `dec_solve` is called to determine whether the goal is reachable given these
    equations;
  - `get` is called by the interpreter to obtain concrete value to build a trace
    leading to the goal;
  - The same process can be repeated for further goals, in that case the
    constraints added by previous calls to `set_to` remain valid.

\subsection specificity Specificity of the string solver

The specificity of the solver is in what kind of expressions `set_to` accepts
and understands. `string_refinementt::set_to` accepts all constraints that are
normally accepted by `bv_refinementt`.

`string_refinementt::set_to` also understands constraints of the form:
  * `char_pointer1 = b ? char_pointer2 : char_pointer3` where `char_pointer<i>`
    variables are of type pointer to characters and `b` is a Boolean
    expression.
  * `i = cprover_primitive(args)` where `i` is of signed bit vector type.
    String primitives are listed in the next section.

\note In the implementation, equations that are not of these forms are passed
  to an embedded `bv_refinementt` solver.

\subsection string-representation String representation in the solver

String primitives can have arguments which are pointers to characters.
These pointers represent strings.
To each of these pointers the string solver associate a char array
which represents the content of the string.
If the pointer is the address of an actual array in the program they should be
linked by using the primitive `cprover_string_associate_array_to_pointer`.
The length of the array can also be linked to a variable of the program using
 `cprover_string_associate_length_to_array`.

\warning The solver assumes the memory pointed by the arguments is immutable
which is not something that is true in general for C pointers for instance.
Therefore for each transformation on a string, it is assumed the program
allocates a new string before calling a primitive.

\section builtin-functions Builtin functions

String operations are handled as "builtin functions", which can operate in two
modes:
1. constraint generation
2. model evaluation

This is described in more detail \link string_builtin_functiont here. \endlink

\section primitives String primitives

\subsection basic-primitives Basic access:

  * `cprover_string_associate_array_to_pointer` : Link with an array of
    characters of the program.
  * `cprover_string_associate_length_to_array` : Link the length of the array
    with the given integer value.
  * `cprover_string_char_at` :
  \copybrief string_constraint_generatort::add_axioms_for_char_at(const function_application_exprt &f)
  \link  string_constraint_generatort::add_axioms_for_char_at More... \endlink
  * `cprover_string_length` :
  \copybrief string_constraint_generatort::add_axioms_for_length(const function_application_exprt &f)
  \link string_constraint_generatort::add_axioms_for_length More... \endlink

\subsection comparisons Comparisons:

  * `cprover_string_compare_to` :
   \copybrief string_constraint_generatort::add_axioms_for_compare_to(const function_application_exprt &f)
   \link string_constraint_generatort::add_axioms_for_compare_to(const function_application_exprt &f) More... \endlink
  * `cprover_string_contains` :
  \copybrief string_constraint_generatort::add_axioms_for_contains(const function_application_exprt &f)
  \link string_constraint_generatort::add_axioms_for_contains(const function_application_exprt &f) More... \endlink
  * `cprover_string_equals` :
  \copybrief string_constraint_generatort::add_axioms_for_equals(const function_application_exprt &f)
  \link string_constraint_generatort::add_axioms_for_equals(const function_application_exprt &f) More... \endlink
  * `cprover_string_equals_ignore_case` :
  \copybrief string_constraint_generatort::add_axioms_for_equals_ignore_case(const function_application_exprt &f)
  \link string_constraint_generatort::add_axioms_for_equals_ignore_case(const function_application_exprt &f) More... \endlink
  * `cprover_string_is_prefix` :
  \copybrief string_constraint_generatort::add_axioms_for_is_prefix
  \link string_constraint_generatort::add_axioms_for_is_prefix More... \endlink
  * `cprover_string_index_of` :
  \copybrief string_constraint_generatort::add_axioms_for_index_of(const function_application_exprt &f=)
  \link string_constraint_generatort::add_axioms_for_index_of(const function_application_exprt &f) More... \endlink
  * `cprover_string_last_index_of` :
  \copybrief string_constraint_generatort::add_axioms_for_last_index_of(const function_application_exprt &f)
  \link string_constraint_generatort::add_axioms_for_last_index_of(const function_application_exprt &f)  More... \endlink

\subsection transformations Transformations:

  * `cprover_string_char_set` :
    \copybrief string_set_char_builtin_functiont::constraints
    \link string_set_char_builtin_functiont::constraints More... \endlink
  * `cprover_string_concat` :
    \copybrief string_constraint_generatort::add_axioms_for_concat
    \link string_constraint_generatort::add_axioms_for_concat More... \endlink
  * `cprover_string_delete` :
    \copybrief string_constraint_generatort::add_axioms_for_delete(const function_application_exprt &f)
    \link string_constraint_generatort::add_axioms_for_delete(const function_application_exprt &f) More... \endlink
  * `cprover_string_insert` :
    \copybrief string_insertion_builtin_functiont::constraints(string_constraint_generatort &generator) const
    \link string_insertion_builtin_functiont::constraints(string_constraint_generatort &generator) const More... \endlink
  * `cprover_string_replace` :
    \copybrief string_constraint_generatort::add_axioms_for_replace(const function_application_exprt &f)
    \link string_constraint_generatort::add_axioms_for_replace(const function_application_exprt &f) More... \endlink
  * `cprover_string_set_length` :
    \copybrief string_constraint_generatort::add_axioms_for_set_length(const function_application_exprt &f)
    \link string_constraint_generatort::add_axioms_for_set_length(const function_application_exprt &f) More... \endlink
  * `cprover_string_substring` :
    \copybrief string_constraint_generatort::add_axioms_for_substring(const function_application_exprt &f)
    \link string_constraint_generatort::add_axioms_for_substring(const function_application_exprt &f) More... \endlink
  * `cprover_string_to_lower_case` :
    \copybrief string_to_lower_case_builtin_functiont::constraints
    \link string_to_lower_case_builtin_functiont::constraints More... \endlink
  * `cprover_string_to_upper_case` :
    \copybrief string_to_upper_case_builtin_functiont::constraints
    \link string_to_upper_case_builtin_functiont::constraints More... \endlink
  * `cprover_string_trim` :
    \copybrief string_constraint_generatort::add_axioms_for_trim(const function_application_exprt &f)
    \link string_constraint_generatort::add_axioms_for_trim(const function_application_exprt &f) More... \endlink

\subsection conversions Conversions:

  * `cprover_string_format` :
    \copybrief add_axioms_for_format
    \link add_axioms_for_format More... \endlink
  * `cprover_string_from_literal` :
    \copybrief string_constraint_generatort::add_axioms_from_literal(const function_application_exprt &f)
    \link string_constraint_generatort::add_axioms_from_literal(const function_application_exprt &f) More... \endlink
  * `cprover_string_of_int` :
    \copybrief string_constraint_generatort::add_axioms_for_string_of_int
    \link string_constraint_generatort::add_axioms_for_string_of_int More... \endlink
  * `cprover_string_of_float` :
    \copybrief string_constraint_generatort::add_axioms_for_string_of_float
    \link string_constraint_generatort::add_axioms_for_string_of_float More... \endlink
  * `cprover_string_of_float_scientific_notation` :
    \copybrief string_constraint_generatort::add_axioms_from_float_scientific_notation
    \link string_constraint_generatort::add_axioms_from_float_scientific_notation More... \endlink
  * `cprover_string_parse_int` :
    \copybrief string_constraint_generatort::add_axioms_for_parse_int
    \link string_constraint_generatort::add_axioms_for_parse_int More... \endlink

\subsection solvers-deprecated Deprecated primitives:

  * `cprover_string_concat_code_point`, `cprover_string_code_point_at`,
    `cprover_string_code_point_before`, `cprover_string_code_point_count`:
    Java specific, should be part of Java models.
  * `cprover_string_offset_by_code_point`, `cprover_string_concat_char`,
    `cprover_string_concat_int`, `cprover_string_concat_long`,
    `cprover_string_concat_bool`, `cprover_string_concat_double`,
    `cprover_string_concat_float` :
    Should be done in two steps: conversion from primitive type and call
    to the string primitive.
  * `cprover_string_array_of_char_pointer`, `cprover_string_to_char_array` :
     Pointer to char array association
     is now handled by `string_constraint_generatort`, there is no need for
     explicit conversion.
  * `cprover_string_is_empty` :
    Should use `cprover_string_length(s) == 0` instead.
  * `cprover_string_is_suffix` : Should use `cprover_string_is_prefix` with an
   offset argument.
  * `cprover_string_empty_string` : Can use literal of empty string instead.
  * `cprover_string_of_long` : Should be the same as `cprover_string_of_int`.
  * `cprover_string_delete_char_at` : A call to
    `cprover_string_delete_char_at(s, i)` would be the same thing as
    `cprover_string_delete(s, i, i+1)`.
  * `cprover_string_copy` : Same as `cprover_string_substring(s, 0)`.
  * `cprover_string_of_int_hex` : Same as `cprover_string_of_int(s, 16)`.
  * `cprover_string_of_double` : Same as `cprover_string_of_float`.

\section algorithm Decision algorithm

\copydetails string_refinementt::dec_solve

\subsection instantiation Instantiation

This is done by generate_instantiations(const index_set_pairt &index_set, const string_axiomst &axioms, const std::unordered_map<string_not_contains_constraintt, symbol_exprt> &not_contain_witnesses).
\copydetails generate_instantiations(const index_set_pairt &index_set, const string_axiomst &axioms, const std::unordered_map<string_not_contains_constraintt, symbol_exprt> &not_contain_witnesses).

\subsection axiom-check Axiom check

\copydetails check_axioms(const string_axiomst &axioms, string_constraint_generatort &generator, const std::function<exprt(const exprt &)> &get, messaget::mstreamt &stream, const namespacet &ns, bool use_counter_example, const union_find_replacet &symbol_resolve, const std::unordered_map<string_not_contains_constraintt, symbol_exprt> &not_contain_witnesses)
\link check_axioms(const string_axiomst &axioms, string_constraint_generatort &generator, const std::function<exprt(const exprt &)> &get, messaget::mstreamt &stream, const namespacet &ns, bool use_counter_example, const union_find_replacet &symbol_resolve, const std::unordered_map<string_not_contains_constraintt, symbol_exprt> &not_contain_witnesses)
  (See function documentation...) \endlink

\section floatbv Floatbv Directory

This library contains the code that is used to convert floating point
variables (`floatbv`) to bit vectors (`bv`).  This is referred to as
‘bit-blasting’ and is called in the `solver` code during conversion to
SAT or SMT. It also contains the abstraction code described in the
FMCAD09 paper.
