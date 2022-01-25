/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#include "utils.h"

#include <goto-programs/cfg.h>

#include <util/fresh_symbol.h>
#include <util/graph.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

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

void havoc_assigns_targetst::append_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  if(expr.id() == ID_pointer_object)
  {
    append_object_havoc_code_for_expr(location, expr.operands().front(), dest);
    return;
  }

  havoc_utilst::append_havoc_code_for_expr(location, expr, dest);
}

void add_pragma_disable_pointer_checks(source_locationt &location)
{
  location.add_pragma("disable:pointer-check");
  location.add_pragma("disable:pointer-primitive-check");
  location.add_pragma("disable:pointer-overflow-check");
  location.add_pragma("disable:signed-overflow-check");
  location.add_pragma("disable:unsigned-overflow-check");
  location.add_pragma("disable:conversion-check");
}

goto_programt::instructiont &
add_pragma_disable_pointer_checks(goto_programt::instructiont &instr)
{
  add_pragma_disable_pointer_checks(instr.source_location_nonconst());
  return instr;
}

goto_programt &add_pragma_disable_pointer_checks(goto_programt &prog)
{
  Forall_goto_program_instructions(it, prog)
    add_pragma_disable_pointer_checks(*it);
  return prog;
}

void add_pragma_disable_assigns_check(source_locationt &location)
{
  location.add_pragma(CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK);
}

goto_programt::instructiont &
add_pragma_disable_assigns_check(goto_programt::instructiont &instr)
{
  add_pragma_disable_assigns_check(instr.source_location_nonconst());
  return instr;
}

goto_programt &add_pragma_disable_assigns_check(goto_programt &prog)
{
  Forall_goto_program_instructions(it, prog)
    add_pragma_disable_assigns_check(*it);
  return prog;
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
    type, id2string(location.get_function()), suffix, location, mode, symtab);
  new_symbol.is_auxiliary = is_auxiliary;
  return new_symbol;
}

void simplify_gotos(goto_programt &goto_program, namespacet &ns)
{
  for(auto &instruction : goto_program.instructions)
  {
    if(
      instruction.is_goto() &&
      simplify_expr(instruction.get_condition(), ns).is_false())
      instruction.turn_into_skip();
  }
}

bool is_loop_free(
  const goto_programt &goto_program,
  namespacet &ns,
  messaget &log)
{
  // create cfg from instruction list
  cfg_baset<empty_cfg_nodet> cfg;
  cfg(goto_program);

  // check that all nodes are there
  INVARIANT(
    goto_program.instructions.size() == cfg.size(),
    "Instruction list vs CFG size mismatch.");

  // compute SCCs
  using idxt = graph_nodet<empty_cfg_nodet>::node_indext;
  std::vector<idxt> node_to_scc(cfg.size(), -1);
  auto nof_sccs = cfg.SCCs(node_to_scc);

  // compute size of each SCC
  std::vector<int> scc_size(nof_sccs, 0);
  for(auto scc : node_to_scc)
  {
    INVARIANT(
      0 <= scc && scc < nof_sccs, "Could not determine SCC for instruction");
    scc_size[scc]++;
  }

  // check they are all of size 1
  for(size_t scc_id = 0; scc_id < nof_sccs; scc_id++)
  {
    auto size = scc_size[scc_id];
    if(size > 1)
    {
      log.error() << "Found CFG SCC with size " << size << messaget::eom;
      for(const auto &node_id : node_to_scc)
      {
        if(node_to_scc[node_id] == scc_id)
        {
          const auto &pc = cfg[node_id].PC;
          goto_program.output_instruction(ns, "", log.error(), *pc);
          log.error() << messaget::eom;
        }
      }
      return false;
    }
  }
  return true;
}

/// Prefix for comments added to track assigns clause replacement.
static const char ASSIGNS_CLAUSE_REPLACEMENT_TRACKING[] =
  " (assigned by the contract of ";

irep_idt make_assigns_clause_replacement_tracking_comment(
  const exprt &target,
  const irep_idt &function_id,
  const namespacet &ns)
{
  return from_expr(ns, target.id(), target) +
         ASSIGNS_CLAUSE_REPLACEMENT_TRACKING + id2string(function_id) + ")";
}

bool is_assigns_clause_replacement_tracking_comment(const irep_idt &comment)
{
  return id2string(comment).find(ASSIGNS_CLAUSE_REPLACEMENT_TRACKING) !=
         std::string::npos;
}
