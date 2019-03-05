/*******************************************************************\

Module: Local variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

/// \file
/// Local variables whose address is taken

#include "dirty.h"

#include <util/std_expr.h>

void dirtyt::build(const goto_functiont &goto_function)
{
  for(const auto &i : goto_function.body.instructions)
    i.apply([this](const exprt &e) { find_dirty(e); });
}

void dirtyt::find_dirty(const exprt &expr)
{
  if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(expr);
    find_dirty_address_of(address_of_expr.object());
    return;
  }

  forall_operands(it, expr)
    find_dirty(*it);
}

void dirtyt::find_dirty_address_of(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=
      to_symbol_expr(expr).get_identifier();

    dirty.insert(identifier);
  }
  else if(expr.id()==ID_member)
  {
    find_dirty_address_of(to_member_expr(expr).struct_op());
  }
  else if(expr.id()==ID_index)
  {
    find_dirty_address_of(to_index_expr(expr).array());
    find_dirty(to_index_expr(expr).index());
  }
  else if(expr.id()==ID_dereference)
  {
    find_dirty(to_dereference_expr(expr).pointer());
  }
  else if(expr.id()==ID_if)
  {
    find_dirty_address_of(to_if_expr(expr).true_case());
    find_dirty_address_of(to_if_expr(expr).false_case());
    find_dirty(to_if_expr(expr).cond());
  }
}

void dirtyt::output(std::ostream &out) const
{
  die_if_uninitialized();
  for(const auto &d : dirty)
    out << d << '\n';
}

/// Analyse the given function with dirtyt if it hasn't been seen before
/// \param id: function id to analyse
/// \param function: function to analyse
void incremental_dirtyt::populate_dirty_for_function(
  const irep_idt &id, const goto_functionst::goto_functiont &function)
{
  auto insert_result = dirty_processed_functions.insert(id);
  if(insert_result.second)
    dirty.add_function(function);
}
