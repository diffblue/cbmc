/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/
#include "dfcc_infer_loop_assigns.h"

#include <util/find_symbols.h>
#include <util/pointer_expr.h>

#include <goto-programs/goto_inline.h>

#include <analyses/goto_rw.h>
#include <analyses/local_may_alias.h>
#include <goto-instrument/contracts/utils.h>

#include "dfcc_loop_nesting_graph.h"
#include "dfcc_root_object.h"

/// Builds a call expression `object_whole(expr)`
static exprt
make_object_whole_call_expr(const exprt &expr, const namespacet &ns)
{
  const symbolt &object_whole_sym = ns.lookup(CPROVER_PREFIX "object_whole");
  const code_typet &object_whole_code_type =
    to_code_type(object_whole_sym.type);
  return side_effect_expr_function_callt(
    object_whole_sym.symbol_expr(),
    {{expr}},
    object_whole_code_type.return_type(),
    expr.source_location());
}

/// Returns true iff \p expr contains at least one identifier found in
/// \p identifiers.
static bool
depends_on(const exprt &expr, std::unordered_set<irep_idt> identifiers)
{
  const std::unordered_set<irep_idt> ids = find_symbol_identifiers(expr);
  for(const auto &id : ids)
  {
    if(identifiers.find(id) != identifiers.end())
      return true;
  }
  return false;
}

/// Collect identifiers that are local to this loop.
/// A identifier is or is equivalent to a loop local if
/// 1. it is declared inside the loop, or
/// 2. there is no write or read of it outside the loop.
/// 3. it is not used in loop contracts.
std::unordered_set<irep_idt> gen_loop_locals_set(
  const irep_idt &function_id,
  goto_functiont &goto_function,
  const dfcc_loop_nesting_graph_nodet &loop_node,
  message_handlert &message_handler,
  const namespacet &ns)
{
  std::unordered_set<irep_idt> loop_locals;
  std::unordered_set<irep_idt> non_loop_locals;

  const auto &loop = loop_node.instructions;

  // All identifiers declared outside the loop.
  std::unordered_set<irep_idt> non_loop_decls;
  // Ranges of all read/write outside the loop.
  rw_range_sett non_loop_rw_range_set(ns, message_handler);

  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    // All variables declared in loops are loop locals.
    if(i_it->is_decl() && loop.contains(i_it))
    {
      loop_locals.insert(i_it->decl_symbol().identifier());
    }
    // Record all other declared variables and their ranges.
    else if(i_it->is_decl())
    {
      non_loop_decls.insert(i_it->decl_symbol().identifier());
    }
    // Record all writing/reading outside the loop.
    else if(
      (i_it->is_assign() || i_it->is_function_call()) && !loop.contains(i_it))
    {
      goto_rw(function_id, i_it, non_loop_rw_range_set);
    }
  }

  // Check if declared variables are loop locals.
  for(const auto &decl_id : non_loop_decls)
  {
    bool is_loop_local = true;
    // No write to the declared variable.
    for(const auto &writing_rw : non_loop_rw_range_set.get_w_set())
    {
      if(decl_id == writing_rw.first)
      {
        is_loop_local = false;
        break;
      }
    }

    // No read to the declared variable.
    for(const auto &writing_rw : non_loop_rw_range_set.get_r_set())
    {
      if(decl_id == writing_rw.first)
      {
        is_loop_local = false;
        break;
      }
    }

    const auto latch_target = loop_node.latch;

    // Loop locals are not used in loop contracts.
    for(const auto &id :
        find_symbol_identifiers(get_loop_assigns(latch_target)))
    {
      if(decl_id == id)
      {
        is_loop_local = false;
        break;
      }
    }

    for(const auto &id :
        find_symbol_identifiers(get_loop_invariants(latch_target, false)))
    {
      if(decl_id == id)
      {
        is_loop_local = false;
        break;
      }
    }

    for(const auto &id :
        find_symbol_identifiers(get_loop_decreases(latch_target, false)))
    {
      if(decl_id == id)
      {
        is_loop_local = false;
        break;
      }
    }

    // Collect all loop locals.
    if(is_loop_local)
      loop_locals.insert(decl_id);
  }

  return loop_locals;
}

/// Find all identifiers in `src`.
static std::unordered_set<irep_idt>
find_symbol_identifiers(const goto_programt &src)
{
  std::unordered_set<irep_idt> identifiers;
  for(const auto &instruction : src.instructions)
  {
    // compute forward edges first
    switch(instruction.type())
    {
    case ASSERT:
    case ASSUME:
    case GOTO:
      find_symbols(instruction.condition(), identifiers);
      break;

    case FUNCTION_CALL:
      find_symbols(instruction.call_lhs(), identifiers);
      for(const auto &e : instruction.call_arguments())
        find_symbols(e, identifiers);
      break;
    case ASSIGN:
    case OTHER:

    case SET_RETURN_VALUE:
    case DECL:
    case DEAD:
      for(const auto &e : instruction.code().operands())
      {
        find_symbols(e, identifiers);
      }
      break;

    case END_THREAD:
    case END_FUNCTION:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
    case SKIP:
    case LOCATION:
    case CATCH:
    case THROW:
    case START_THREAD:
      break;
    case NO_INSTRUCTION_TYPE:
    case INCOMPLETE_GOTO:
      UNREACHABLE;
      break;
    }
  }
  return identifiers;
}

/// Infer loop assigns in the given `loop`. Loop assigns should depend
/// on some identifiers in `candidate_targets`. `function_assigns_map`
/// contains the function contracts used to infer loop assigns of
/// function_call instructions.
static assignst dfcc_infer_loop_assigns_for_loop(
  const local_may_aliast &local_may_alias,
  goto_functiont &goto_function,
  const dfcc_loop_nesting_graph_nodet &loop,
  const std::unordered_set<irep_idt> &candidate_targets,
  message_handlert &message_handler,
  const namespacet &ns)
{
  // infer
  assignst assigns;
  infer_loop_assigns(local_may_alias, loop.instructions, assigns);

  // compute locals
  std::unordered_set<irep_idt> loop_locals =
    gen_loop_locals_set(irep_idt(), goto_function, loop, message_handler, ns);

  // widen or drop targets that depend on loop-locals or are non-constant,
  // ie. depend on other locations assigned by the loop.
  // e.g: if the loop assigns {i, a[i]}, then a[i] is non-constant.
  havoc_utils_can_forward_propagatet is_constant(assigns, ns);
  assignst result;
  for(const auto &expr : assigns)
  {
    // Skip targets that only depend on non-visible identifiers.
    if(!depends_on(expr, candidate_targets))
    {
      continue;
    }

    if(depends_on(expr, loop_locals))
    {
      // Target depends on loop locals, attempt widening to the root object
      auto root_objects = dfcc_root_objects(expr);
      for(const auto &root_object : root_objects)
      {
        if(!depends_on(root_object, loop_locals))
        {
          address_of_exprt address_of_root_object(root_object);
          address_of_root_object.add_source_location() =
            root_object.source_location();
          result.emplace(
            make_object_whole_call_expr(address_of_root_object, ns));
        }
      }
    }
    else
    {
      address_of_exprt address_of_expr(expr);
      address_of_expr.add_source_location() = expr.source_location();
      // Widen assigns targets to object_whole if `expr` is a dereference or
      // with constant address.
      if(expr.id() == ID_dereference || !is_constant(address_of_expr))
      {
        // Target address is not constant, widening to the whole object
        result.emplace(make_object_whole_call_expr(address_of_expr, ns));
      }
      else
      {
        result.emplace(expr);
      }
    }
  }

  return result;
}

/// Remove assignments to `__CPROVER_dead_object` to avoid aliasing all targets
/// that are assigned to `__CPROVER_dead_object`.
static void remove_dead_object_assignment(goto_functiont &goto_function)
{
  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_assign())
    {
      auto &lhs = i_it->assign_lhs();

      if(
        lhs.id() == ID_symbol &&
        to_symbol_expr(lhs).identifier() == CPROVER_PREFIX "dead_object")
      {
        i_it->turn_into_skip();
      }
    }
  }
}

void dfcc_infer_loop_assigns_for_function(
  std::map<std::size_t, assignst> &inferred_loop_assigns_map,
  goto_functionst &goto_functions,
  const goto_functiont &goto_function,
  message_handlert &message_handler,
  const namespacet &ns)
{
  messaget log(message_handler);

  // Collect all candidate targets---identifiers visible in `goto_function`.
  const auto candidate_targets = find_symbol_identifiers(goto_function.body);

  // We infer loop assigns based on the copy of `goto_function`.
  goto_functiont goto_function_copy;
  goto_function_copy.copy_from(goto_function);

  // Build the loop id map before inlining attempt. So that we can later
  // distinguish loops in the original body and loops added by inlining.
  const auto loop_nesting_graph =
    build_loop_nesting_graph(goto_function_copy.body);
  auto topsorted = loop_nesting_graph.topsort();
  // skip function without loop.
  if(topsorted.empty())
    return;

  // Map from targett in `goto_function_copy` to loop number.
  std::
    unordered_map<goto_programt::const_targett, std::size_t, const_target_hash>
      loop_number_map;

  for(const auto id : topsorted)
  {
    loop_number_map.emplace(
      loop_nesting_graph[id].head, loop_nesting_graph[id].latch->loop_number);
  }

  // We avoid inlining `malloc` and `free` whose variables are not assigns.
  auto malloc_body = goto_functions.function_map.extract(irep_idt("malloc"));
  auto free_body = goto_functions.function_map.extract(irep_idt("free"));

  // Inline all function calls in goto_function_copy; this is best-effort
  // inlining, we can safely ignore warnings here.
  null_message_handlert null_message_handler;
  goto_program_inline(
    goto_functions, goto_function_copy.body, ns, null_message_handler);
  // Update the body to make sure all goto correctly jump to valid targets.
  goto_function_copy.body.update();
  // Build the loop graph after inlining.
  const auto inlined_loop_nesting_graph =
    build_loop_nesting_graph(goto_function_copy.body);

  // Alias analysis.
  remove_dead_object_assignment(goto_function_copy);
  local_may_aliast local_may_alias(goto_function_copy);

  auto inlined_topsorted = inlined_loop_nesting_graph.topsort();

  for(const auto inlined_id : inlined_topsorted)
  {
    // We only infer loop assigns for loops in the original function.
    if(
      loop_number_map.find(inlined_loop_nesting_graph[inlined_id].head) !=
      loop_number_map.end())
    {
      const auto loop_number =
        loop_number_map[inlined_loop_nesting_graph[inlined_id].head];
      const auto inlined_loop = inlined_loop_nesting_graph[inlined_id];

      inferred_loop_assigns_map[loop_number] = dfcc_infer_loop_assigns_for_loop(
        local_may_alias,
        goto_function_copy,
        inlined_loop,
        candidate_targets,
        message_handler,
        ns);
    }
  }
  // Restore the function boyd of `malloc` and `free`.
  goto_functions.function_map.insert(std::move(malloc_body));
  goto_functions.function_map.insert(std::move(free_body));
}
