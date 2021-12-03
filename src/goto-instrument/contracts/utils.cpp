/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#include "utils.h"

#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>

goto_programt::instructiont &
add_pragma_disable_assigns_check(goto_programt::instructiont &instr)
{
  instr.source_location_nonconst().add_pragma(
    CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK);
  return instr;
}

goto_programt &add_pragma_disable_assigns_check(goto_programt &prog)
{
  Forall_goto_program_instructions(it, prog)
    add_pragma_disable_assigns_check(*it);
  return prog;
}

static void append_safe_havoc_code_for_expr(
  const source_locationt location,
  const namespacet &ns,
  const exprt &expr,
  goto_programt &dest,
  const std::function<void()> &havoc_code_impl)
{
  goto_programt skip_program;
  const auto skip_target = skip_program.add(goto_programt::make_skip(location));

  // skip havocing only if all pointer derefs in the expression are valid
  // (to avoid spurious pointer deref errors)
  dest.add(goto_programt::make_goto(
    skip_target, not_exprt{all_dereferences_are_valid(expr, ns)}, location));

  havoc_code_impl();

  // add the final skip target
  dest.destructive_append(skip_program);
}

void havoc_if_validt::append_object_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  append_safe_havoc_code_for_expr(location, ns, expr, dest, [&]() {
    havoc_utilst::append_object_havoc_code_for_expr(location, expr, dest);
  });
}

void havoc_if_validt::append_scalar_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  append_safe_havoc_code_for_expr(location, ns, expr, dest, [&]() {
    havoc_utilst::append_scalar_havoc_code_for_expr(location, expr, dest);
  });
}

exprt all_dereferences_are_valid(const exprt &expr, const namespacet &ns)
{
  exprt::operandst validity_checks;

  if(expr.id() == ID_dereference)
    validity_checks.push_back(
      good_pointer_def(to_dereference_expr(expr).pointer(), ns));

  for(const auto &op : expr.operands())
    validity_checks.push_back(all_dereferences_are_valid(op, ns));

  return conjunction(validity_checks);
}

exprt generate_lexicographic_less_than_check(
  const std::vector<symbol_exprt> &lhs,
  const std::vector<symbol_exprt> &rhs)
{
  PRECONDITION(lhs.size() == rhs.size());

  if(lhs.empty())
  {
    return false_exprt();
  }

  // Store conjunctions of equalities.
  // For example, suppose that the two input vectors are <s1, s2, s3> and <l1,
  // l2, l3>.
  // Then this vector stores <s1 == l1, s1 == l1 && s2 == l2,
  // s1 == l1 && s2 == l2 && s3 == l3>.
  // In fact, the last element is unnecessary, so we do not create it.
  exprt::operandst equality_conjunctions(lhs.size());
  equality_conjunctions[0] = binary_relation_exprt(lhs[0], ID_equal, rhs[0]);
  for(size_t i = 1; i < equality_conjunctions.size() - 1; i++)
  {
    binary_relation_exprt component_i_equality{lhs[i], ID_equal, rhs[i]};
    equality_conjunctions[i] =
      and_exprt(equality_conjunctions[i - 1], component_i_equality);
  }

  // Store inequalities between the i-th components of the input vectors
  // (i.e. lhs and rhs).
  // For example, suppose that the two input vectors are <s1, s2, s3> and <l1,
  // l2, l3>.
  // Then this vector stores <s1 < l1, s1 == l1 && s2 < l2, s1 == l1 &&
  // s2 == l2 && s3 < l3>.
  exprt::operandst lexicographic_individual_comparisons(lhs.size());
  lexicographic_individual_comparisons[0] =
    binary_relation_exprt(lhs[0], ID_lt, rhs[0]);
  for(size_t i = 1; i < lexicographic_individual_comparisons.size(); i++)
  {
    binary_relation_exprt component_i_less_than{lhs[i], ID_lt, rhs[i]};
    lexicographic_individual_comparisons[i] =
      and_exprt(equality_conjunctions[i - 1], component_i_less_than);
  }
  return disjunction(lexicographic_individual_comparisons);
}

void insert_before_swap_and_advance(
  goto_programt &destination,
  goto_programt::targett &target,
  goto_programt &payload)
{
  const auto offset = payload.instructions.size();
  destination.insert_before_swap(target, payload);
  std::advance(target, offset);
}

const symbolt &new_tmp_symbol(
  const typet &type,
  const source_locationt &location,
  const irep_idt &mode,
  symbol_table_baset &symtab,
  std::string suffix,
  bool is_auxiliary)
{
  symbolt &new_symbol = get_fresh_aux_symbol(
    type,
    id2string(location.get_function()) + "::",
    suffix,
    location,
    mode,
    symtab);
  new_symbol.is_auxiliary = is_auxiliary;
  return new_symbol;
}

void disable_pointer_checks(source_locationt &source_location)
{
  source_location.add_pragma("disable:pointer-check");
  source_location.add_pragma("disable:pointer-primitive-check");
  source_location.add_pragma("disable:pointer-overflow-check");
}
