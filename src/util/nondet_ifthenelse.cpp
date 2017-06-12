/*******************************************************************\

Module: Nondeterministic if-then-else

Author: Chris Smowton, chris@smowton.net

\*******************************************************************/

/// \file
/// Nondeterministic if-then-else

#include "nondet_ifthenelse.h"

#include <sstream>

#include <util/nondet_bool.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/source_location.h>

// This will be unified with other similar fresh-symbol routines shortly
static symbolt &new_tmp_symbol(
  symbol_tablet &symbol_table,
  const std::string &prefix,
  const irep_idt &mode)
{
  static size_t temporary_counter=0;

  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;

  do
  {
    new_symbol.name="tmp_object_factory$"+std::to_string(++temporary_counter);
    new_symbol.base_name=new_symbol.name;
    new_symbol.mode=mode;
  }
  while(symbol_table.move(new_symbol, symbol_ptr));

  return *symbol_ptr;
}

/// Emits instructions and defines labels for the beginning of a
/// nondeterministic if-else diamond. Code is emitted to the `result_code`
/// member of this object's associated `java_object_factoryt` instance `state`.
/// The caller should use the following pattern (where *this is an instance of
/// java_object_factoryt): ``` nondet_ifthenelset diamond(*this, "name");
/// diamond.begin_if(); result_code.copy_to_operands(Some if-branch code)
/// diamond.begin_else(); result_code.copy_to_operands(Some else-branch code)
/// diamond.finish(); ```
void nondet_ifthenelset::begin_if()
{
  static size_t nondet_ifthenelse_count=0;

  auto choice_sym=
    new_tmp_symbol(symbol_table, choice_symname, fresh_symbol_mode);
  choice_sym.type=c_bool_typet(1);
  auto choice=choice_sym.symbol_expr();
  auto assign_choice=
    code_assignt(choice, get_nondet_bool(choice_sym.type));
  assign_choice.add_source_location()=loc;
  result_code.move_to_operands(assign_choice);

  std::ostringstream fresh_label_oss;
  fresh_label_oss << choice_symname << "_else_"
                  << (++nondet_ifthenelse_count);
  std::string fresh_label=fresh_label_oss.str();
  else_label=code_labelt(fresh_label, code_skipt());

  std::ostringstream done_label_oss;
  done_label_oss << choice_symname << "_done_"
                 << nondet_ifthenelse_count;
  join_label=code_labelt(done_label_oss.str(), code_skipt());

  code_ifthenelset test;
  test.cond()=equal_exprt(
    choice,
    constant_exprt("0", choice_sym.type));
  test.then_case()=code_gotot(fresh_label);
  result_code.move_to_operands(test);
}

/// Terminates the if-block and begins the else-block of a nondet if-then-else
/// diamond. See ::begin_if for detail.
void nondet_ifthenelset::begin_else()
{
  result_code.copy_to_operands(code_gotot(join_label.get_label()));
  result_code.copy_to_operands(else_label);
}

/// Concludes a nondet if-then-else diamond. See ::begin_if for detail.
void nondet_ifthenelset::finish()
{
  result_code.move_to_operands(join_label);
}
