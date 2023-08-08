/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation Utilities

#include "shadow_memory_util.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/ssa_expr.h>
#include <util/std_expr.h>

#include <langapi/language_util.h> // IWYU pragma: keep

// TODO: change DEBUG_SM to DEBUG_SHADOW_MEMORY (it also appears in other files)

irep_idt extract_field_name(const exprt &string_expr)
{
  if(string_expr.id() == ID_typecast)
    return extract_field_name(to_typecast_expr(string_expr).op());
  else if(string_expr.id() == ID_address_of)
    return extract_field_name(to_address_of_expr(string_expr).object());
  else if(string_expr.id() == ID_index)
    return extract_field_name(to_index_expr(string_expr).array());
  else if(string_expr.id() == ID_string_constant)
  {
    return string_expr.get(ID_value);
  }
  else
    UNREACHABLE;
}

/// If the given type is an array type, then remove the L2 level
/// renaming from its size.
/// \param type Type to be modified
static void remove_array_type_l2(typet &type)
{
  if(to_array_type(type).size().id() != ID_symbol)
    return;

  ssa_exprt &size = to_ssa_expr(to_array_type(type).size());
  size.remove_level_2();
}

void clean_pointer_expr(exprt &expr, const typet &type)
{
  if(
    type.id() == ID_array && expr.id() == ID_symbol &&
    to_array_type(type).size().get_bool(ID_C_SSA_symbol))
  {
    remove_array_type_l2(expr.type());
    exprt original_expr = to_ssa_expr(expr).get_original_expr();
    remove_array_type_l2(original_expr.type());
    to_ssa_expr(expr).set_expression(original_expr);
  }
  if(expr.id() == ID_string_constant)
  {
    expr = address_of_exprt(expr);
    expr.type() = pointer_type(char_type());
  }
  else if(expr.id() == ID_dereference)
  {
    expr = to_dereference_expr(expr).pointer();
  }
  else
  {
    expr = address_of_exprt(expr);
  }
  POSTCONDITION(expr.type().id() == ID_pointer);
}

void log_get_field(
  const namespacet &ns,
  const messaget &log,
  const irep_idt &field_name,
  const exprt &expr)
{
  log.conditional_output(
    log.debug(), [ns, field_name, expr](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: get_field: " << id2string(field_name)
              << " for " << format(expr) << messaget::eom;
    });
}

void log_value_set(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, value_set](messaget::mstreamt &mstream) {
      for(const auto &e : value_set)
      {
        mstream << "Shadow memory: value_set: " << format(e) << messaget::eom;
      }
    });
#endif
}

void log_value_set_match(
  const namespacet &ns,
  const messaget &log,
  const shadow_memory_statet::shadowed_addresst &shadowed_address,
  const exprt &matched_base_address,
  const value_set_dereferencet::valuet &dereference,
  const exprt &expr,
  const value_set_dereferencet::valuet &shadow_dereference)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(),
    [ns,
     shadowed_address,
     expr,
     dereference,
     matched_base_address,
     shadow_dereference](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: value_set_match: " << messaget::eom;
      mstream << "Shadow memory:   base: " << format(shadowed_address.address)
              << " <-- " << format(matched_base_address) << messaget::eom;
      mstream << "Shadow memory:   cell: " << format(dereference.pointer)
              << " <-- " << format(expr) << messaget::eom;
      mstream << "Shadow memory:   shadow_ptr: "
              << format(shadow_dereference.pointer) << messaget::eom;
      mstream << "Shadow memory:   shadow_val: "
              << format(shadow_dereference.value) << messaget::eom;
    });
#endif
}

void log_value_set_match(
  const namespacet &ns,
  const messaget &log,
  const exprt &address,
  const exprt &expr)
{
  // Leave guards rename to DEBUG_SHADOW_MEMORY
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, address, expr](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: value_set_match: " << format(address)
              << " <-- " << format(expr) << messaget::eom;
    });
#endif
}

void log_try_shadow_address(
  const namespacet &ns,
  const messaget &log,
  const shadow_memory_statet::shadowed_addresst &shadowed_address)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, shadowed_address](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: trying shadowed address: "
              << format(shadowed_address.address) << messaget::eom;
    });
#endif
}

void log_cond(
  const namespacet &ns,
  const messaget &log,
  const char *cond_text,
  const exprt &cond)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, cond_text, cond](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: " << cond_text << ": " << format(cond)
              << messaget::eom;
    });
#endif
}

static void log_are_types_incompatible(
  const namespacet &ns,
  const exprt &expr,
  const shadow_memory_statet::shadowed_addresst &shadowed_address,
  const messaget &log)
{
#ifdef DEBUG_SM
  log.debug() << "Shadow memory: incompatible types "
              << from_type(ns, "", expr.type()) << ", "
              << from_type(ns, "", shadowed_address.address.type())
              << messaget::eom;
#endif
}
