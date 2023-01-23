/*******************************************************************\

Module: Enumerative Loop Contracts Synthesizer

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerative Loop Contracts Synthesizer

#include "enumerative_loop_contracts_synthesizer.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/find_symbols.h>
#include <util/format_expr.h>
#include <util/pointer_predicates.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>

#include <analyses/natural_loops.h>
#include <goto-instrument/havoc_utils.h>

#include "cegis_verifier.h"
#include "expr_enumerator.h"

// substitute all tmp_post variables with their origins in `expr`
void replace_tmp_post(
  exprt &dest,
  const std::unordered_map<exprt, exprt, irep_hash> &tmp_post_map)
{
  replace_symbolt r;
  for(const auto &tmp_post_entry : tmp_post_map)
  {
    INVARIANT(
      can_cast_expr<symbol_exprt>(tmp_post_entry.first),
      "tmp_post variables must be symbol expression.");
    const auto &tmp_post_symbol =
      expr_dynamic_cast<symbol_exprt>(tmp_post_entry.first);
    r.insert(tmp_post_symbol, tmp_post_entry.second);
  }
  r.replace(dest);
}

std::vector<exprt> construct_terminals(const std::set<symbol_exprt> &symbols)
{
  std::vector<exprt> result;
  for(const auto &e : symbols)
  {
    if(e.type().id() == ID_unsignedbv)
    {
      // For a variable v with primitive type, we add
      // v, __CPROVER_loop_entry(v)
      // into the result.
      result.push_back(typecast_exprt(e, size_type()));
      result.push_back(
        typecast_exprt(unary_exprt(ID_loop_entry, e, e.type()), size_type()));
    }
    if((e.type().id() == ID_signedbv))
    {
      result.push_back(e);
      result.push_back(unary_exprt(ID_loop_entry, e, e.type()));
    }
    if((e.type().id() == ID_pointer))
    {
      // For a variable v with pointer type, we add
      // __CPROVER_pointer_offset(v),
      // __CPROVER_pointer_offset(__CPROVER_loop_entry(v))
      // into the result.
      result.push_back(pointer_offset_exprt(e, size_type()));
      result.push_back(pointer_offset_exprt(
        unary_exprt(ID_loop_entry, e, e.type()), size_type()));
    }
  }
  result.push_back(from_integer(1, unsigned_int_type()));
  result.push_back(from_integer(1, unsigned_long_int_type()));
  return result;
}

void enumerative_loop_contracts_synthesizert::init_candidates()
{
  for(auto &function_p : goto_model.goto_functions.function_map)
  {
    natural_loopst natural_loops;
    natural_loops(function_p.second.body);

    // Initialize invariants for unannotated loops as true
    for(const auto &loop_head_and_content : natural_loops.loop_map)
    {
      goto_programt::const_targett loop_end =
        get_loop_end_from_loop_head_and_content(
          loop_head_and_content.first, loop_head_and_content.second);

      loop_idt new_id(function_p.first, loop_end->loop_number);

      log.debug() << "Initialize candidates for the loop at "
                  << loop_end->source_location() << messaget::eom;

      // we only synthesize invariants and assigns for unannotated loops
      if(loop_end->condition().find(ID_C_spec_loop_invariant).is_nil())
      {
        // Store the loop guard.
        exprt guard =
          get_loop_head(
            loop_end->loop_number,
            goto_model.goto_functions.function_map[function_p.first])
            ->condition();
        neg_guards[new_id] = guard;

        // Initialize invariant clauses as `true`.
        in_invariant_clause_map[new_id] = true_exprt();
        pos_invariant_clause_map[new_id] = true_exprt();

        // Initialize assigns clauses.
        if(loop_end->condition().find(ID_C_spec_assigns).is_nil())
        {
          assigns_map[new_id] = {};
        }
      }
    }
  }
  log.debug() << "Finished candidates initialization." << messaget::eom;
}

void enumerative_loop_contracts_synthesizert::synthesize_assigns(
  const exprt &checked_pointer,
  const std::list<loop_idt> cause_loop_ids)
{
  namespacet ns(goto_model.symbol_table);
  auto new_assign = checked_pointer;

  // Add the new assigns target to the most-inner loop that doesn't contain
  // the new assigns target yet.
  for(const auto &loop_id : cause_loop_ids)
  {
    // Widen index and dereference to whole object.
    if(new_assign.id() == ID_index || new_assign.id() == ID_dereference)
    {
      address_of_exprt address_of_new_assigns(new_assign);
      havoc_utils_is_constantt is_constant(assigns_map[loop_id], ns);
      if(!is_constant(address_of_new_assigns))
      {
        new_assign = pointer_object(address_of_new_assigns);
      }
    }

    const auto &source_location =
      get_loop_head(
        loop_id.loop_number,
        goto_model.goto_functions.function_map[loop_id.function_id])
        ->source_location();

    // Simplify expr to avoid offset that is out of scope.
    // In the case of nested loops, After widening, pointer_object(ptr + i)
    // can contain the pointer ptr in the scope of both loops, and the offset
    // i which is only in the scope of the inner loop.
    // After simplification, pointer_object(ptr + i) -> pointer_object(ptr).
    new_assign = simplify_expr(new_assign, ns);
    new_assign.add_source_location() = source_location;

    // Avoid adding same target.
    if(assigns_map[loop_id].insert(new_assign).second)
      return;
  }
  INVARIANT(false, "Failed to synthesize a new assigns target.");
}

void enumerative_loop_contracts_synthesizert::build_tmp_post_map()
{
  for(auto &goto_function : goto_model.goto_functions.function_map)
  {
    for(const auto &instruction : goto_function.second.body.instructions)
    {
      // tmp_post variables are symbol lhs of ASSIGN.
      if(!instruction.is_assign() || instruction.assign_lhs().id() != ID_symbol)
        continue;

      const auto symbol_lhs =
        expr_try_dynamic_cast<symbol_exprt>(instruction.assign_lhs());

      // tmp_post variables have identifiers with the prefix tmp::tmp_post.
      if(
        id2string(symbol_lhs->get_identifier()).find("tmp::tmp_post") !=
        std::string::npos)
      {
        tmp_post_map[instruction.assign_lhs()] = instruction.assign_rhs();
      }
    }
  }
}

std::set<symbol_exprt>
enumerative_loop_contracts_synthesizert::compute_dependent_symbols(
  const loop_idt &cause_loop_id,
  const exprt &new_clause,
  const std::set<exprt> &live_vars)
{
  // We overapproximate dependent symbols as all symbols in live variables.
  // TODO: using flow-dependency analysis to rule out not dependent symbols.

  std::set<symbol_exprt> result;
  for(const auto &e : live_vars)
    find_symbols(e, result);

  return result;
}

exprt enumerative_loop_contracts_synthesizert::synthesize_range_predicate(
  const exprt &violated_predicate)
{
  // For the case where the violated predicate is dependent on no instruction
  // other than loop havocing, the violated_predicate is
  // WLP(loop_body_before_violation, violated_predicate).
  // TODO: implement a more complete WLP algorithm.
  return violated_predicate;
}

exprt enumerative_loop_contracts_synthesizert::synthesize_same_object_predicate(
  const exprt &checked_pointer)
{
  // The same object predicate says that the checked pointer points to the
  // same object as it pointed before entering the loop.
  // It works for the array-manipulating loops where only offset of pointer
  // are modified but not the object pointers point to.
  return same_object(
    checked_pointer, unary_exprt(ID_loop_entry, checked_pointer));
}

exprt enumerative_loop_contracts_synthesizert::synthesize_strengthening_clause(
  const std::vector<exprt> terminal_symbols,
  const loop_idt &cause_loop_id,
  const irep_idt &violation_id)
{
  // Synthesis of strengthening clauses is a enumerate-and-check process.
  // We first construct the enumerator for the following grammar.
  // And then enumerate clause and check that if it can make the invariant
  // inductive.

  // Initialize factory representing grammar
  // StartBool -> StartBool && StartBool | Start == Start
  //              | StartBool <= StartBool | StartBool < StartBool
  // Start -> Start + Start | terminal_symbols
  // where a0, and a1 are symbol expressions.
  namespacet ns(goto_model.symbol_table);
  enumerator_factoryt factory = enumerator_factoryt(ns);
  recursive_enumerator_placeholdert start_bool_ph(factory, "StartBool", ns);
  recursive_enumerator_placeholdert start_ph(factory, "Start", ns);

  // terminals
  expr_sett leafexprs(terminal_symbols.begin(), terminal_symbols.end());

  // rules for Start
  enumeratorst start_args;
  // Start -> terminals
  leaf_enumeratort leaf_g(leafexprs, ns);
  start_args.push_back(&leaf_g);

  // Start -> Start + Start
  binary_functional_enumeratort plus_g(
    ID_plus,
    start_ph,
    start_ph,
    [](const partitiont &partition) {
      if(partition.size() <= 1)
        return true;
      return partition.front() == 1;
    },
    ns);
  start_args.push_back(&plus_g);

  // rules for StartBool
  enumeratorst start_bool_args;
  // StartBool -> StartBool && StartBool
  binary_functional_enumeratort and_g(ID_and, start_bool_ph, start_bool_ph, ns);
  start_bool_args.push_back(&and_g);
  // StartBool -> Start == Start
  binary_functional_enumeratort equal_g(ID_equal, start_ph, start_ph, ns);
  start_bool_args.push_back(&equal_g);
  // StartBool -> Start <= Start
  binary_functional_enumeratort le_g(ID_le, start_ph, start_ph, ns);
  start_bool_args.push_back(&le_g);
  // StartBool -> Start < Start
  binary_functional_enumeratort lt_g(ID_lt, start_ph, start_ph, ns);
  start_bool_args.push_back(&lt_g);

  // add the two nonterminals to the factory
  factory.attach_productions("Start", start_args);
  factory.attach_productions("StartBool", start_bool_args);

  // size of candidates we are searching now,
  // starting from 0
  size_t size_bound = 0;

  // numbers of candidates we have seen,
  // used for quantitative analysis
  size_t seen_terms = 0;

  // Start to enumerate and check.
  while(true)
  {
    size_bound++;

    // generate candidate and verify
    for(auto strengthening_candidate : start_bool_ph.enumerate(size_bound))
    {
      log.progress() << "Verifying candidate: "
                     << format(strengthening_candidate) << messaget::eom;
      seen_terms++;
      invariant_mapt new_in_clauses = invariant_mapt(in_invariant_clause_map);
      new_in_clauses[cause_loop_id] =
        and_exprt(new_in_clauses[cause_loop_id], strengthening_candidate);
      const auto &combined_invariant = combine_in_and_post_invariant_clauses(
        new_in_clauses, pos_invariant_clause_map, neg_guards);

      // The verifier we use to check current invariant candidates.
      cegis_verifiert verifier(
        combined_invariant, assigns_map, goto_model, log);

      // A good strengthening clause if
      // 1. all checks pass, or
      // 2. the loop invariant is inductive and hold upon the entry.
      const auto &return_cex = verifier.verify();
      if(
        !return_cex.has_value() ||
        (verifier.properties.at(violation_id).status !=
           property_statust::FAIL &&
         return_cex->violation_type !=
           cext::violation_typet::cex_not_hold_upon_entry))
      {
        return strengthening_candidate;
      }
    }
  }
  UNREACHABLE;
}

invariant_mapt enumerative_loop_contracts_synthesizert::synthesize_all()
{
  init_candidates();
  build_tmp_post_map();

  // The invariants we are going to synthesize and verify are the combined
  // invariants from in- and post- invariant clauses.
  auto combined_invariant = combine_in_and_post_invariant_clauses(
    in_invariant_clause_map, pos_invariant_clause_map, neg_guards);

  // The verifier we use to check current invariant candidates.
  cegis_verifiert verifier(combined_invariant, assigns_map, goto_model, log);

  // Set of symbols the violation may be dependent on.
  // We enumerate strengthening clauses built from symbols from the set.
  std::set<symbol_exprt> dependent_symbols;
  // Set of symbols we used to enumerate strengthening clauses.
  std::vector<exprt> terminal_symbols;

  log.debug() << "Start the first synthesis iteration." << messaget::eom;
  auto return_cex = verifier.verify();

  while(return_cex.has_value())
  {
    exprt new_invariant_clause = true_exprt();
    // Synthesize the new_clause
    // We use difference strategies for different type of violations.
    switch(return_cex->violation_type)
    {
    case cext::violation_typet::cex_out_of_boundary:
      new_invariant_clause =
        synthesize_range_predicate(return_cex->violated_predicate);
      break;

    case cext::violation_typet ::cex_null_pointer:
      new_invariant_clause =
        synthesize_same_object_predicate(return_cex->checked_pointer);
      break;

    case cext::violation_typet::cex_not_preserved:
      terminal_symbols = construct_terminals(dependent_symbols);
      new_invariant_clause = synthesize_strengthening_clause(
        terminal_symbols,
        return_cex->cause_loop_ids.front(),
        verifier.target_violation_id);
      break;

    case cext::violation_typet::cex_assignable:
      synthesize_assigns(
        return_cex->checked_pointer, return_cex->cause_loop_ids);
      break;
    case cext::violation_typet::cex_not_hold_upon_entry:
    case cext::violation_typet::cex_other:
      INVARIANT(false, "unsupported violation type");
      break;
    }

    // Assigns map has already been updated in the switch block.
    // Update invariants map for other types of violations.
    if(return_cex->violation_type != cext::violation_typet::cex_assignable)
    {
      INVARIANT(!return_cex->cause_loop_ids.empty(), "No cause loop found!");
      INVARIANT(
        new_invariant_clause != true_exprt(),
        "failed to synthesized meaningful clause");

      // There could be tmp_post variables in the synthesized clause.
      // We substitute them with their original variables.
      replace_tmp_post(new_invariant_clause, tmp_post_map);

      const auto &cause_loop_id = return_cex->cause_loop_ids.front();
      // Update the dependent symbols.
      dependent_symbols = compute_dependent_symbols(
        cause_loop_id, new_invariant_clause, return_cex->live_variables);

      // add the new clause to the candidate invariants.
      if(
        return_cex->violation_location ==
        cext::violation_locationt::in_condition)
      {
        // When the violation happens in the loop guard, the new clause
        // should hold for the both cases of
        // 1. loop guard holds        --- loop_guard -> in_invariant
        // 2. loop guard doesn't hold --- !loop_guard -> pos_invariant
        in_invariant_clause_map[cause_loop_id] = and_exprt(
          in_invariant_clause_map[cause_loop_id], new_invariant_clause);
        pos_invariant_clause_map[cause_loop_id] = and_exprt(
          pos_invariant_clause_map[cause_loop_id], new_invariant_clause);
      }
      else if(
        return_cex->violation_location == cext::violation_locationt::in_loop)
      {
        // When the violation happens in the loop body, the new clause
        // should hold for the case of
        // loop guard holds        --- loop_guard -> in_invariant
        in_invariant_clause_map[cause_loop_id] = and_exprt(
          in_invariant_clause_map[cause_loop_id], new_invariant_clause);
      }
      else
      {
        // When the violation happens after the loop body, the new clause
        // should hold for the case of
        // loop guard doesn't hold --- !loop_guard -> pos_invariant
        pos_invariant_clause_map[cause_loop_id] = and_exprt(
          pos_invariant_clause_map[cause_loop_id], new_invariant_clause);
      }

      // Re-combine invariant clauses and update the candidate map.
      combined_invariant = combine_in_and_post_invariant_clauses(
        in_invariant_clause_map, pos_invariant_clause_map, neg_guards);
    }

    return_cex = verifier.verify();
  }

  log.result() << "result : " << log.green << "PASS" << log.reset
               << messaget::eom;

  return combined_invariant;
}

exprt enumerative_loop_contracts_synthesizert::synthesize(loop_idt loop_id)
{
  return true_exprt();
}
