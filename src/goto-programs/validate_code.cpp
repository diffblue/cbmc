/*******************************************************************\

Module: Validate code

Author: Daniel Poetzl

\*******************************************************************/

#include "validate_code.h"

#ifdef REPORT_UNIMPLEMENTED_CODE_CHECKS
#  include <iostream>
#endif

#include <util/goto_instruction_code.h>
#include <util/std_code.h>
#include <util/validate_helpers.h>

#define CALL_ON_CODE(code_type)                                                \
  C<codet, code_type>()(code, std::forward<Args>(args)...)

template <template <typename, typename> class C, typename... Args>
void call_on_code(const codet &code, Args &&... args)
{
  if(code.get_statement() == ID_assign)
  {
    CALL_ON_CODE(code_assignt);
  }
  else if(code.get_statement() == ID_decl)
  {
    CALL_ON_CODE(code_declt);
  }
  else if(code.get_statement() == ID_dead)
  {
    CALL_ON_CODE(code_deadt);
  }
  else if(code.get_statement() == ID_function_call)
  {
    CALL_ON_CODE(code_function_callt);
  }
  else if(code.get_statement() == ID_return)
  {
    CALL_ON_CODE(code_returnt);
  }
  else if(code.get_statement() == ID_block)
  {
    CALL_ON_CODE(code_blockt);
  }
  else
  {
#ifdef REPORT_UNIMPLEMENTED_CODE_CHECKS
    std::cerr << "Unimplemented well-formedness check for code statement with "
                 "id: "
              << code.get_statement().id_string() << std::endl;
#endif

    CALL_ON_CODE(codet);
  }
}

/// Check that the given code statement is well-formed (shallow checks only,
/// i.e., enclosed statements, subexpressions, etc. are not checked)
///
/// The function determines the type `T` of the statement `code` (by inspecting
/// the `id()` field) and then calls `T::check(code, vm)`.
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void check_code(const codet &code, const validation_modet vm)
{
  call_on_code<call_checkt>(code, vm);
}

/// Check that the given code statement is well-formed, assuming that all its
/// enclosed statements, subexpressions, etc. have already been checked for
/// well-formedness.
///
/// The function determines the type `T` of the statement `code` (by inspecting
/// the `id()` field) and then calls `T::validate(code, ns, vm)`.
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void validate_code(
  const codet &code,
  const namespacet &ns,
  const validation_modet vm)
{
  call_on_code<call_validatet>(code, ns, vm);
}

/// Check that the given code statement is well-formed (full check, including
/// checks of all subexpressions)
///
/// The function determines the type `T` of the statement `code` (by inspecting
/// the `id()` field) and then calls `T::validate_full(code, ns, vm)`.
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void validate_full_code(
  const codet &code,
  const namespacet &ns,
  const validation_modet vm)
{
  call_on_code<call_validate_fullt>(code, ns, vm);
}
