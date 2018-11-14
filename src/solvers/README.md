\ingroup module_hidden
\defgroup solvers solvers
# Folder solvers

\authors Romain Brenguier, Kareem Khazem, Martin Brain

\section solvers-overview Overview

The basic role of solvers is to answer whether the set of equations given
is satisfiable.
One example usage, is to determine whether an assertion in a
program can be violated.
We refer to \ref goto-symex for how CBMC and JBMC convert a input program
and property to a set of equations.

The secondary role of solvers is to provide a satisfying assignment of
the variables of the equations, this can for instance be used to construct
a trace.

The `solvers/` directory contains interfaces to a number of
different decision procedures, roughly one per directory.

* prop/:   The basic and common functionality. The key file is
  `prop_conv.h` which defines `prop_convt`.  This is the base class that
  is used to interface to the decision procedures. The key functions are
  `convert` which takes an `exprt` and converts it to the appropriate,
  solver specific, data structures and `dec_solve` (inherited from
  `decision_proceduret`) which invokes the actual decision procedures.
  Individual decision procedures (named `*_dect`) objects can be created
  but `prop_convt` is the preferred interface for code that uses them.

* flattening/:   A library that converts operations to bit-vectors,
  including calling the conversions in `floatbv` as necessary. Is
  implemented as a simple conversion (with caching) and then a
  post-processing function that adds extra constraints. This is not used
  by the SMT or CVC back-ends.

* dplib/:   Provides the `dplib_dect` object which used the decision
  procedure library from “Decision Procedures : An Algorithmic Point of
  View”.

* cvc/:   Provides the `cvc_dect` type which interfaces to the old (pre
  SMTLib) input format for the CVC family of solvers.  This format is
  still supported by depreciated in favour of SMTLib 2.

* smt1/:   Provides the `smt1_dect` type which converts the formulae to
  SMTLib version 1 and then invokes one of Boolector, CVC3, OpenSMT,
  Yices, MathSAT or Z3. Again, note that this format is depreciated.

* smt2/:   Provides the `smt2_dect` type which functions in a similar
  way to `smt1_dect`, calling Boolector, CVC3, MathSAT, Yices or Z3.
  Note that the interaction with the solver is batched and uses
  temporary files rather than using the interactive command supported by
  SMTLib 2. With the `–fpa` option, this output mode will not flatten
  the floating point arithmetic and instead output the proposed SMTLib
  floating point standard.

* qbf/:   Back-ends for a variety of QBF solvers. Appears to be no
  longer used or maintained.

* sat/:   Back-ends for a variety of SAT solvers and DIMACS output.

\section flattening-section Flattening

To be documented.

\section solver-apis Solver APIs

\subsection smt-solving-api-section SMT solving API

To be documented.

\subsection sat-solving-api-section SAT solving API

To be documented.

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
* \ref bmct

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

\section primitives String primitives

\subsection basic-primitives Basic access:

  * `cprover_string_associate_array_to_pointer` : Link with an array of
    characters of the program.
  * `cprover_string_associate_length_to_array` : Link the length of the array
    with the given integer value.
  * `cprover_string_char_at` :
  \copybrief add_axioms_for_char_at(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
  \link  add_axioms_for_char_at More... \endlink
  * `cprover_string_length` :
  \copybrief add_axioms_for_length(const function_application_exprt &f, array_poolt &array_pool)
  \link add_axioms_for_length More... \endlink

\subsection comparisons Comparisons:

  * `cprover_string_compare_to` :
   \copybrief add_axioms_for_compare_to(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool)
   \link add_axioms_for_compare_to(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_contains` :
  \copybrief add_axioms_for_contains(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool)
  \link add_axioms_for_contains(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_equals` :
  \copybrief add_axioms_for_equals(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool)
  \link add_axioms_for_equals(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_equals_ignore_case` :
  \copybrief add_axioms_for_equals_ignore_case(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool)
  \link add_axioms_for_equals_ignore_case(symbol_generatort &fresh_symbol,const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_hash_code` :
  \copybrief string_constraint_generatort::add_axioms_for_hash_code
  \link string_constraint_generatort::add_axioms_for_hash_code More... \endlink
  * `cprover_string_is_prefix` :
  \copybrief add_axioms_for_is_prefix
  \link add_axioms_for_is_prefix More... \endlink
  * `cprover_string_index_of` :
  \copybrief add_axioms_for_index_of(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
  \link add_axioms_for_index_of(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_last_index_of` :
  \copybrief add_axioms_for_last_index_of(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
  \link add_axioms_for_last_index_of(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)  More... \endlink

\subsection transformations Transformations:

  * `cprover_string_char_set` :
    \copybrief string_set_char_builtin_functiont::constraints
    \link string_set_char_builtin_functiont::constraints More... \endlink
  * `cprover_string_concat` :
    \copybrief add_axioms_for_concat
    \link add_axioms_for_concat More... \endlink
  * `cprover_string_delete` :
    \copybrief add_axioms_for_delete(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_for_delete(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_insert` :
    \copybrief add_axioms_for_insert(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_for_insert(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_replace` :
    \copybrief add_axioms_for_replace(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_for_replace(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_set_length` :
    \copybrief add_axioms_for_set_length(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_for_set_length(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_substring` :
    \copybrief add_axioms_for_substring(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_for_substring(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_to_lower_case` :
    \copybrief string_to_lower_case_builtin_functiont::constraints
    \link string_to_lower_case_builtin_functiont::constraints More... \endlink
  * `cprover_string_to_upper_case` :
    \copybrief string_to_upper_case_builtin_functiont::constraints
    \link string_to_upper_case_builtin_functiont::constraints More... \endlink
  * `cprover_string_trim` :
    \copybrief add_axioms_for_trim(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_for_trim(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink

\subsection conversions Conversions:

  * `cprover_string_format` :
    \copybrief add_axioms_for_format
    \link add_axioms_for_format More... \endlink
  * `cprover_string_from_literal` :
    \copybrief add_axioms_from_literal(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_from_literal(symbol_generatort &fresh_symbol, const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_of_int` :
    \copybrief add_axioms_for_string_of_int
    \link add_axioms_for_string_of_int More... \endlink
  * `cprover_string_of_float` :
    \copybrief add_axioms_for_string_of_float
    \link add_axioms_for_string_of_float More... \endlink
  * `cprover_string_of_float_scientific_notation` :
    \copybrief add_axioms_from_float_scientific_notation
    \link add_axioms_from_float_scientific_notation More... \endlink
  * `cprover_string_of_char` :
    \copybrief add_axioms_from_char(const function_application_exprt &f, array_poolt &array_pool)
    \link add_axioms_from_char(const function_application_exprt &f, array_poolt &array_pool) More... \endlink
  * `cprover_string_parse_int` :
    \copybrief add_axioms_for_parse_int
    \link add_axioms_for_parse_int More... \endlink

\subsection solvers-deprecated Deprecated primitives:

  * `cprover_string_concat_code_point`, `cprover_string_code_point_at`,
    `cprover_string_code_point_before`, `cprover_string_code_point_count`:
    Java specific, should be part of Java models.
  * `cprover_string_offset_by_code_point`, `cprover_string_concat_char`,
    `cprover_string_concat_int`, `cprover_string_concat_long`,
    `cprover_string_concat_bool`, `cprover_string_concat_double`,
    `cprover_string_concat_float`, `cprover_string_insert_int`,
    `cprover_string_insert_long`, `cprover_string_insert_bool`,
    `cprover_string_insert_char`, `cprover_string_insert_double`,
     `cprover_string_insert_float` :
    Should be done in two steps: conversion from primitive type and call
    to the string primitive.
  * `cprover_string_array_of_char_pointer`, `cprover_string_to_char_array` :
     Pointer to char array association
     is now handled by `string_constraint_generatort`, there is no need for
     explicit conversion.
  * `cprover_string_intern` : Never tested.
  * `cprover_string_is_empty` :
    Should use `cprover_string_length(s) == 0` instead.
  * `cprover_string_is_suffix` : Should use `cprover_string_is_prefix` with an
   offset argument.
  * `cprover_string_empty_string` : Can use literal of empty string instead.
  * `cprover_string_of_long` : Should be the same as `cprover_string_of_int`.
  * `cprover_string_delete_char_at` : A call to
    `cprover_string_delete_char_at(s, i)` would be the same thing as
    `cprover_string_delete(s, i, i+1)`.
  * `cprover_string_of_bool` :
    Language dependent, should be implemented in the models.
  * `cprover_string_copy` : Same as `cprover_string_substring(s, 0)`.
  * `cprover_string_of_int_hex` : Same as `cprover_string_of_int(s, 16)`.
  * `cprover_string_of_double` : Same as `cprover_string_of_float`.

\section algorithm Decision algorithm

\copydetails string_refinementt::dec_solve

\subsection instantiation Instantiation

This is done by generate_instantiations(messaget::mstreamt &stream, const string_constraint_generatort &generator, const index_set_pairt &index_set, const string_axiomst &axioms, const std::map<string_not_contains_constraintt, symbol_exprt> &not_contain_witnesses).
\copydetails generate_instantiations(messaget::mstreamt &stream, const string_constraint_generatort &generator, const index_set_pairt &index_set, const string_axiomst &axioms, const std::map<string_not_contains_constraintt, symbol_exprt> &not_contain_witnesses).

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
