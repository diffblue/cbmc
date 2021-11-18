/*******************************************************************\

Module: Data structures representing instructions in a GOTO program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Data structures representing instructions in a GOTO program

#include "goto_instruction_code.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

code_inputt::code_inputt(
  std::vector<exprt> arguments,
  optionalt<source_locationt> location)
  : codet{ID_input, std::move(arguments)}
{
  if(location)
    add_source_location() = std::move(*location);
  check(*this, validation_modet::INVARIANT);
}

code_inputt::code_inputt(
  const irep_idt &description,
  exprt expression,
  optionalt<source_locationt> location)
  : code_inputt{{address_of_exprt(index_exprt(
                   string_constantt(description),
                   from_integer(0, index_type()))),
                 std::move(expression)},
                std::move(location)}
{
}

void code_inputt::check(const codet &code, const validation_modet vm)
{
  DATA_CHECK(
    vm, code.operands().size() >= 2, "input must have at least two operands");
}

code_outputt::code_outputt(
  std::vector<exprt> arguments,
  optionalt<source_locationt> location)
  : codet{ID_output, std::move(arguments)}
{
  if(location)
    add_source_location() = std::move(*location);
  check(*this, validation_modet::INVARIANT);
}

code_outputt::code_outputt(
  const irep_idt &description,
  exprt expression,
  optionalt<source_locationt> location)
  : code_outputt{{address_of_exprt(index_exprt(
                    string_constantt(description),
                    from_integer(0, index_type()))),
                  std::move(expression)},
                 std::move(location)}
{
}

void code_outputt::check(const codet &code, const validation_modet vm)
{
  DATA_CHECK(
    vm, code.operands().size() >= 2, "output must have at least two operands");
}

inline code_function_callt
havoc_slice_call(const exprt &p, const exprt &size, const namespacet &ns)
{
  irep_idt identifier = CPROVER_PREFIX "havoc_slice";
  symbol_exprt havoc_slice_function = ns.lookup(identifier).symbol_expr();
  code_function_callt::argumentst arguments = {p, size};
  return code_function_callt{std::move(havoc_slice_function),
                             std::move(arguments)};
}
