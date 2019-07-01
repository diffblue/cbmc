/*******************************************************************\

Module: Java trace validation

Author: Jeannie Moulton

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_TRACE_VALIDATION_H
#define CPROVER_JAVA_BYTECODE_JAVA_TRACE_VALIDATION_H

#include <util/optional.h>
#include <util/validation_mode.h>

class goto_tracet;
class namespacet;
class exprt;
class address_of_exprt;
class constant_exprt;
class struct_exprt;
class symbol_exprt;
class member_exprt;
class messaget;

// clang-format off
#define OPT_JAVA_TRACE_VALIDATION /*NOLINT*/ \
  "(validate-trace)" \

#define HELP_JAVA_TRACE_VALIDATION /*NOLINT*/ \
    " --validate-trace             throw an error if the structure of the counterexample\n" /*NOLINT*/ \
    "                              trace does not match certain assumptions\n" /*NOLINT*/ \
    "                              (experimental, currently java only)\n" /*NOLINT*/ \
// clang-format on

/// Checks that the structure of each step of the trace matches certain
/// criteria. If it does not, throw an error. Intended to be called by
/// the caller of \ref build_goto_trace, for example
/// \ref java_multi_path_symex_checkert::build_full_trace()
void check_trace_assumptions(
  const goto_tracet &trace,
  const namespacet &ns,
  const messaget &log,
  const bool run_check = false,
  const validation_modet vm = validation_modet::INVARIANT);

/// \return true iff the expression is a symbol expression and has a non-empty
/// identifier
bool check_symbol_structure(const exprt &expr);

/// Recursively extracts the first operand of an expression until it reaches a
/// symbol and returns it, or returns an empty optional
optionalt<symbol_exprt> get_inner_symbol_expr(exprt expr);

/// \return true iff the expression is a member expression (or nested member
/// expression) of a valid symbol
bool check_member_structure(const member_exprt &expr);

/// \return true iff the left hand side is superficially an expected expression
/// type
bool valid_lhs_expr_high_level(const exprt &lhs);

/// \return true iff the right hand side is superficially an expected expression
/// type
bool valid_rhs_expr_high_level(const exprt &rhs);

/// \return true iff the expression is a constant or symbol expression, i.e.,
/// one that can be evaluated to a literal, as for for a index value
bool can_evaluate_to_constant(const exprt &expression);

/// \return true iff the expression is an index expression and has a valid
/// symbol and index value as operands
bool check_index_structure(const exprt &index_expr);

/// \return true iff the struct expression and has valid operands
bool check_struct_structure(const struct_exprt &expr);

/// \return true iff the address_of_exprt has a valid symbol operand
bool check_address_structure(const address_of_exprt &address);

/// \return true iff the constant_exprt has valid operands and value
bool check_constant_structure(const constant_exprt &constant_expr);

#endif // CPROVER_JAVA_BYTECODE_JAVA_TRACE_VALIDATION_H
