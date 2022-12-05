/*******************************************************************\

Module: Enumerative Loop Invariant Synthesizer

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerative Loop Invariant Synthesizer

#include "enumerative_loop_invariant_synthesizer.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/find_symbols.h>
#include <util/format_expr.h>
#include <util/pointer_predicates.h>

#include <analyses/natural_loops.h>

#include "cegis_verifier.h"
#include "expr_enumerator.h"

// substitute all tmp_post variables with their origins in `expr`
void substitute_tmp_post_rec(
  exprt &dest,
  const std::map<exprt, exprt> &tmp_post_map)
{
  if(dest.id() != ID_address_of)
    Forall_operands(it, dest)
      substitute_tmp_post_rec(*it, tmp_post_map);

  // possibly substitute?
  if(dest.id() == ID_symbol && tmp_post_map.count(dest))
  {
    dest = tmp_post_map.at(dest);
  }
}

std::vector<exprt> construct_terminals(std::set<symbol_exprt> symbols)
{
  std::vector<exprt> result = std::vector<exprt>();
  for(const auto &e : symbols)
  {
    if(e.type().id() == ID_unsignedbv)
    {
      // For a variable v with primitive type, we add
      // v, __CPROVER_loop_entry(v)
      // into the result.
      result.push_back(e);
      result.push_back(unary_exprt(ID_loop_entry, e, size_type()));
    }
    if((e.type().id() == ID_pointer))
    {
      // For a variable v with pointer type, we add
      // __CPROVER_pointer_offset(v),
      // __CPROVER_pointer_offset(__CPROVER_loop_entry(v))
      // into the result.
      result.push_back(unary_exprt(ID_pointer_offset, e, size_type()));
      result.push_back(pointer_offset_exprt(
        unary_exprt(ID_loop_entry, e, e.type()), size_type()));
    }
  }
  result.push_back(from_integer(1, size_type()));
  return result;
}

void enumerative_loop_invariant_synthesizert::init_candidates()
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

      // we only synthesize invariants for unannotated loops
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
      }
    }
  }
}

void enumerative_loop_invariant_synthesizert::build_tmp_post_map()
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
enumerative_loop_invariant_synthesizert::compute_dependent_symbols(
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

exprt enumerative_loop_invariant_synthesizert::synthesize_range_predicate(
  const exprt &violated_predicate)
{
  // For the case where the violated predicate is dependent on no instruction
  // other than loop havocing, the violated_predicate is
  // WLP(loop_body_before_violation, violated_predicate).
  // TODO: implement a more complete WLP algorithm.
  return violated_predicate;
}

exprt enumerative_loop_invariant_synthesizert::synthesize_same_object_predicate(
  const exprt &checked_pointer)
{
  // The same object predicate says that the checked pointer points to the
  // same object as it pointed before entering the loop.
  // It works for the array-manuplating loops where only offset of pointer
  // are modified but not the object pointers point to.
  return same_object(
    checked_pointer, unary_exprt(ID_loop_entry, checked_pointer));
}

exprt enumerative_loop_invariant_synthesizert::synthesize_strengthening_clause(
  const std::vector<exprt> terminal_symbols,
  const loop_idt &cause_loop_id,
  const irep_idt &violation_id)
{
  // Synthesis of strengthning clauses is a enumerate-and-check proecess.
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
      seen_terms++;
      invariant_mapt new_in_clauses = invariant_mapt(in_invariant_clause_map);
      new_in_clauses[cause_loop_id] =
        and_exprt(new_in_clauses[cause_loop_id], strengthening_candidate);
      const auto &combined_invariant = combine_in_and_post_invariant_clauses(
        new_in_clauses, pos_invariant_clause_map, neg_guards);

      // The verifier we use to check current invariant candidates.
      cegis_verifiert verifier(combined_invariant, goto_model, log);

      // A good strengthening clause if
      // 1. all checks pass, or
      // 2. the loop invariant is inductive and hold upon the entry.
      if(
        verifier.verify() || (verifier.properties.at(violation_id).status !=
                                property_statust::FAIL &&
                              verifier.return_cex.cex_type !=
                                cext::violation_typet::cex_not_hold_upon_entry))
      {
        return strengthening_candidate;
      }
    }
  }
  UNREACHABLE;
}

invariant_mapt enumerative_loop_invariant_synthesizert::synthesize_all()
{
  init_candidates();
  build_tmp_post_map();

  // The invariants we are going to synthesize and verify are the combined
  // invariants from in- and pos- invariant clauses.
  auto combined_invariant = combine_in_and_post_invariant_clauses(
    in_invariant_clause_map, pos_invariant_clause_map, neg_guards);

  // The verifier we use to check current invariant candidates.
  cegis_verifiert verifier(combined_invariant, goto_model, log);

  // Set of symbols the violation may be dependent on.
  // We enumerate strenghening clauses built from symbols from the set.
  std::set<symbol_exprt> dependent_symbols;
  // Set of symbols we used to enumerate strenghening clauses.
  std::vector<exprt> terminal_symbols;

  while(!verifier.verify())
  {
    exprt new_invariant_clause = true_exprt();

    // Synthsize the new_clause
    // We use difference strategies for different type of violations.
    switch(verifier.return_cex.cex_type)
    {
    case cext::violation_typet::cex_out_of_boundary:
      new_invariant_clause =
        synthesize_range_predicate(verifier.return_cex.violated_predicate);
      break;

    case cext::violation_typet ::cex_null_pointer:
      new_invariant_clause =
        synthesize_same_object_predicate(verifier.return_cex.checked_pointer);
      break;

    case cext::violation_typet::cex_not_preserved:
      terminal_symbols = construct_terminals(dependent_symbols);
      new_invariant_clause = synthesize_strengthening_clause(
        terminal_symbols,
        verifier.return_cex.cause_loop_id,
        verifier.first_violation);
      break;

    case cext::violation_typet::cex_not_hold_upon_entry:
    case cext::violation_typet::cex_other:
      INVARIANT(false, "unsupported violation type");
      break;
    }

    INVARIANT(
      new_invariant_clause != true_exprt(),
      "failed to synthesized meaningful clause");

    // There could be tmp_post varialbes in the synthesized clause.
    // We substitute them with their original variables.
    substitute_tmp_post_rec(new_invariant_clause, tmp_post_map);

    // Update the dependent symbols.
    dependent_symbols = compute_dependent_symbols(
      verifier.return_cex.cause_loop_id,
      new_invariant_clause,
      verifier.return_cex.live_variables);

    // add the new cluase to the candidate invairants
    if(verifier.return_cex.is_violation_in_loop)
    {
      in_invariant_clause_map[verifier.return_cex.cause_loop_id] = and_exprt(
        in_invariant_clause_map[verifier.return_cex.cause_loop_id],
        new_invariant_clause);
    }
    else
    {
      // violation happens pos-loop.
      pos_invariant_clause_map[verifier.return_cex.cause_loop_id] = and_exprt(
        pos_invariant_clause_map[verifier.return_cex.cause_loop_id],
        new_invariant_clause);
    }

    // Re-combine invariant clauses and update the candidate map.
    combined_invariant = combine_in_and_post_invariant_clauses(
      in_invariant_clause_map, pos_invariant_clause_map, neg_guards);
  }

  log.result() << "result : " << log.green << "PASS" << messaget::eom
               << log.reset;

  return combined_invariant;
}

exprt enumerative_loop_invariant_synthesizert::synthesize(loop_idt loop_id)
{
  return true_exprt();
}
