/*******************************************************************\

Module: Dynamic frame condition checking for function and loop contracts.

Author: Qinheping Hu, qinhh@amazon.com
Author: Remi Delmas delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_cfg_info.h"

#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>

#include <analyses/local_may_alias.h>
#include <analyses/natural_loops.h>
#include <goto-instrument/contracts/utils.h>

#include "dfcc_check_loop_normal_form.h"
#include "dfcc_infer_loop_assigns.h"
#include "dfcc_is_cprover_symbol.h"
#include "dfcc_library.h"
#include "dfcc_loop_nesting_graph.h"
#include "dfcc_loop_tags.h"
#include "dfcc_root_object.h"
#include "dfcc_utils.h"

/// Extracts the assigns clause expression from the latch condition
static const exprt::operandst &
get_assigns(const goto_programt::const_targett &latch_target)
{
  return static_cast<const exprt &>(
           latch_target->condition().find(ID_C_spec_assigns))
    .operands();
}

/// Extracts the invariant clause expression from the latch condition
static const exprt::operandst &
get_invariants(const goto_programt::const_targett &latch_target)
{
  return static_cast<const exprt &>(
           latch_target->condition().find(ID_C_spec_loop_invariant))
    .operands();
}

/// Extracts the decreases clause expression from the latch condition
static const exprt::operandst &
get_decreases(const goto_programt::const_targett &latch_target)
{
  return static_cast<const exprt &>(
           latch_target->condition().find(ID_C_spec_decreases))
    .operands();
}

/// Returns true iff some contract clause expression is attached
/// to the latch condition of this loop
static bool has_contract(const goto_programt::const_targett &latch_target)
{
  return !get_assigns(latch_target).empty() ||
         !get_invariants(latch_target).empty() ||
         !get_decreases(latch_target).empty();
}

void dfcc_loop_infot::output(std::ostream &out) const
{
  out << "dfcc_loop_id: " << loop_id << "\n";
  out << "cbmc_loop_id: " << cbmc_loop_id << "\n";
  out << "local: {";
  for(auto &id : local)
  {
    out << id << ", ";
  }
  out << "}\n";

  out << "tracked: {";
  for(auto &id : tracked)
  {
    out << id << ", ";
  }
  out << "}\n";

  out << "write_set: " << format(write_set_var) << "\n";

  out << "addr_of_write_set: " << format(addr_of_write_set_var) << "\n";

  out << "assigns: {";
  for(auto &expr : assigns)
  {
    out << format(expr) << ", ";
  }
  out << "}\n";

  out << "invariant: " << format(invariant) << "\n";

  out << "decreases: {";
  for(auto &expr : decreases)
  {
    out << format(expr) << ", ";
  }
  out << "}\n";

  out << "inner loops: {"
      << "\n";
  for(auto &id : inner_loops)
  {
    out << id << ", ";
  }
  out << "}\n";

  out << "outer loops: {"
      << "\n";
  for(auto &id : outer_loops)
  {
    out << id << ", ";
  }
  out << "}\n";
}

optionalt<goto_programt::targett>
dfcc_loop_infot::find_head(goto_programt &goto_program) const
{
  for(auto target = goto_program.instructions.begin();
      target != goto_program.instructions.end();
      target++)
  {
    if(dfcc_is_loop_head(target) && dfcc_has_loop_id(target, loop_id))
    {
      return target;
    }
  }
  return {};
}

optionalt<goto_programt::targett>
dfcc_loop_infot::find_latch(goto_programt &goto_program) const
{
  optionalt<goto_programt::targett> result = nullopt;
  for(auto target = goto_program.instructions.begin();
      target != goto_program.instructions.end();
      target++)
  {
    // go until the end because we want to find the very last occurrence
    if(dfcc_is_loop_latch(target) && dfcc_has_loop_id(target, loop_id))
    {
      result = target;
    }
  }
  return result;
}

static optionalt<goto_programt::targett> check_has_contract_rec(
  const dfcc_loop_nesting_grapht &loop_nesting_graph,
  const std::size_t loop_idx,
  const bool must_have_contract)
{
  const auto &node = loop_nesting_graph[loop_idx];
  if(must_have_contract && !has_contract(node.latch))
    return node.head;

  for(const auto pred_idx : loop_nesting_graph.get_predecessors(loop_idx))
  {
    auto result = check_has_contract_rec(
      loop_nesting_graph, pred_idx, has_contract(node.latch));
    if(result.has_value())
      return result;
  }
  return {};
}

/// Traverses the loop nesting graph from top level loops and checks if all
/// loops nested in loops that have contracts also have contracts.
/// Return the head of the first offending loop if it exists, nothing otherwise.
static optionalt<goto_programt::targett> check_inner_loops_have_contracts(
  const dfcc_loop_nesting_grapht &loop_nesting_graph)
{
  for(std::size_t idx = 0; idx < loop_nesting_graph.size(); idx++)
  {
    if(loop_nesting_graph.get_successors(idx).empty())
    {
      auto result = check_has_contract_rec(loop_nesting_graph, idx, false);
      if(result.has_value())
        return result;
    }
  }
  return {};
}

/// Tags instructions of loops found in \p loop_nesting_graph with the loop
/// identifier of the innermost loop it belongs to, and the loop instruction
/// type : head, body, exiting or latch.
static void tag_loop_instructions(
  goto_programt &goto_program,
  dfcc_loop_nesting_grapht &loop_nesting_graph)
{
  for(const auto &idx : loop_nesting_graph.topsort())
  {
    auto &node = loop_nesting_graph[idx];
    auto &head = node.head;
    auto &latch = node.latch;
    auto &instruction_iterators = node.instructions;

    dfcc_set_loop_head(head);
    dfcc_set_loop_latch(latch);

    for(goto_programt::targett t : instruction_iterators)
    {
      // Skip instructions that are already tagged and belong to inner loops.
      auto loop_id_opt = dfcc_get_loop_id(t);
      if(loop_id_opt.has_value())
        continue;

      dfcc_set_loop_id(t, idx);

      if(t != head && t != latch)
        dfcc_set_loop_body(t);

      if(t->is_goto() && !instruction_iterators.contains(t->get_target()))
      {
        dfcc_set_loop_exiting(t);
      }
    }
  }

  auto top_level_id = loop_nesting_graph.size();

  // tag remaining instructions as top level
  for(auto target = goto_program.instructions.begin();
      target != goto_program.instructions.end();
      target++)
  {
    // Skip instructions that are already tagged (belong to loops).
    auto loop_id_opt = dfcc_get_loop_id(target);
    if(loop_id_opt.has_value())
    {
      continue;
    }
    dfcc_set_loop_id(target, top_level_id);
    dfcc_set_loop_top_level(target);
  }
}

static bool is_assigned(dirtyt &dirty, const irep_idt &ident, assignst assigns)
{
  PRECONDITION(!dirty(ident));
  // For each assigns clause target
  for(const auto &expr : assigns)
  {
    auto root_objects = dfcc_root_objects(expr);
    for(const auto &root_object : root_objects)
    {
      if(
        root_object.id() == ID_symbol &&
        expr_try_dynamic_cast<symbol_exprt>(root_object)->get_identifier() ==
          ident)
      {
        return true;
      }
      // If `root_object` is not a symbol, then it contains a combination of
      // address-of and dereference operators that cannot be statically
      // resolved to a symbol.
      // Since we know `ident` is not dirty, we know that dereference
      // operations cannot land on that `ident`. So the root_object cannot
      // describe a memory location within the object backing that ident.
      // We conclude that ident is not assigned by this target and move on to
      // the next target.
    }
  }
  return false;
}

/// Collect identifiers that are local to this loop only
/// (excluding nested loop).
static std::unordered_set<irep_idt> gen_loop_locals_set(
  const dfcc_loop_nesting_grapht &loop_nesting_graph,
  const std::size_t loop_id)
{
  std::unordered_set<irep_idt> loop_locals;
  for(const auto &target : loop_nesting_graph[loop_id].instructions)
  {
    auto loop_id_opt = dfcc_get_loop_id(target);
    if(
      target->is_decl() && loop_id_opt.has_value() &&
      loop_id_opt.value() == loop_id)
    {
      loop_locals.insert(target->decl_symbol().get_identifier());
    }
  }
  return loop_locals;
}

/// Compute subset of locals that must be tracked in the loop's write set.
/// A local must be tracked if it is dirty or if it may be assigned by one
/// of the inner loops.
/// To understand why, just consider what would happen in this situation:
/// The loop-local must be declared in the assigns clause of the inner loop
/// otherwise assigns clause checking for the inner loop would fail (from the
/// point of view of the inner loop, that variable is non-local).
/// Since write sets inclusion checks are performed between a loop and its
/// immediately inner loops,  if a loop-local variable
/// that's dirty or that is assigned by an inner loop is not tracked in the
/// loop's write set the inclusion check between the loop write set and inner
/// loop would fail, because the inner loop contains a location that cannot be
/// found in the outer loop's write set.
static std::unordered_set<irep_idt> gen_tracked_set(
  const std::vector<std::size_t> &inner_loops_ids,
  const std::unordered_set<irep_idt> &locals,
  dirtyt &dirty,
  const std::map<std::size_t, dfcc_loop_infot> &loop_info_map)
{
  std::unordered_set<irep_idt> tracked;
  for(const auto &ident : locals)
  {
    if(dirty(ident))
    {
      tracked.insert(ident);
    }
    else
    {
      // Check if this ident is touched by one of the inner loops
      for(const auto inner_loop_id : inner_loops_ids)
      {
        if(is_assigned(dirty, ident, loop_info_map.at(inner_loop_id).assigns))
          tracked.insert(ident);
      }
    }
  }
  return tracked;
}

struct contract_clausest
{
  explicit contract_clausest(const exprt::operandst &decreases)
    : invariant_expr(nil_exprt()), assigns(), decreases_clauses(decreases)
  {
  }
  exprt invariant_expr;
  assignst assigns;
  exprt::operandst decreases_clauses;
};

/// Generate defaults for all contract clauses of the loop with ID `loop_id` if
/// at least one type of clause is defined
static struct contract_clausest default_loop_contract_clauses(
  const dfcc_loop_nesting_grapht &loop_nesting_graph,
  const std::size_t loop_id,
  const irep_idt &function_id,
  local_may_aliast &local_may_alias,
  message_handlert &message_handler,
  const namespacet &ns)
{
  messaget log(message_handler);
  const auto &loop = loop_nesting_graph[loop_id];

  // Process loop contract clauses
  exprt::operandst invariant_clauses = get_invariants(loop.latch);
  exprt::operandst assigns_clauses = get_assigns(loop.latch);

  // Initialise defaults
  struct contract_clausest result(get_decreases(loop.latch));

  // Generate defaults for all clauses if at least one type of clause is defined
  if(
    !invariant_clauses.empty() || !result.decreases_clauses.empty() ||
    !assigns_clauses.empty())
  {
    if(invariant_clauses.empty())
    {
      // use a default invariant if none given.
      result.invariant_expr = true_exprt{};
      // assigns clause is missing; we will try to automatic inference
      log.warning() << "No invariant provided for loop " << function_id << "."
                    << loop.latch->loop_number << " at "
                    << loop.head->source_location()
                    << ". Using 'true' as a sound default invariant. Please "
                       "provide an invariant the default is too weak."
                    << messaget::eom;
    }
    else
    {
      // conjoin all invariant clauses
      result.invariant_expr = conjunction(invariant_clauses);
    }

    // unpack assigns clause targets
    if(!assigns_clauses.empty())
    {
      for(auto &operand : assigns_clauses)
      {
        result.assigns.insert(operand);
      }
    }
    else
    {
      // infer assigns clause targets if none given
      auto inferred = dfcc_infer_loop_assigns(
        local_may_alias, loop.instructions, loop.head->source_location(), ns);
      log.warning() << "No assigns clause provided for loop " << function_id
                    << "." << loop.latch->loop_number << " at "
                    << loop.head->source_location() << ". The inferred set {";
      bool first = true;
      for(const auto &expr : inferred)
      {
        if(!first)
        {
          log.warning() << ", ";
        }
        first = false;
        log.warning() << format(expr);
      }
      log.warning() << "} might be incomplete or imprecise, please provide an "
                       "assigns clause if the analysis fails."
                    << messaget::eom;
      result.assigns.swap(inferred);
    }

    if(result.decreases_clauses.empty())
    {
      log.warning() << "No decrease clause provided for loop " << function_id
                    << "." << loop.latch->loop_number << " at "
                    << loop.head->source_location()
                    << ". Termination will not be checked." << messaget::eom;
    }
  }
  return result;
}

static dfcc_loop_infot gen_dfcc_loop_info(
  const dfcc_loop_nesting_grapht &loop_nesting_graph,
  const std::size_t loop_id,
  const irep_idt &function_id,
  const std::map<std::size_t, dfcc_loop_infot> &loop_info_map,
  dirtyt &dirty,
  local_may_aliast &local_may_alias,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  symbol_tablet &symbol_table)
{
  std::unordered_set<irep_idt> loop_locals =
    gen_loop_locals_set(loop_nesting_graph, loop_id);

  std::unordered_set<irep_idt> loop_tracked = gen_tracked_set(
    loop_nesting_graph.get_predecessors(loop_id),
    loop_locals,
    dirty,
    loop_info_map);

  const namespacet ns(symbol_table);
  struct contract_clausest contract_clauses = default_loop_contract_clauses(
    loop_nesting_graph,
    loop_id,
    function_id,
    local_may_alias,
    message_handler,
    ns);

  std::set<std::size_t> inner_loops;
  for(auto pred_idx : loop_nesting_graph.get_predecessors(loop_id))
  {
    inner_loops.insert(pred_idx);
  }

  std::set<std::size_t> outer_loops;
  for(auto succ_idx : loop_nesting_graph.get_successors(loop_id))
  {
    outer_loops.insert(succ_idx);
  }

  auto &loop = loop_nesting_graph[loop_id];
  const auto cbmc_loop_number = loop.latch->loop_number;
  const auto &language_mode = utils.get_function_symbol(function_id).mode;

  // Generate "write set" variable
  const auto &write_set_var =
    get_fresh_aux_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET],
      id2string(function_id),
      "__write_set_loop_" + std::to_string(cbmc_loop_number),
      loop.head->source_location(),
      language_mode,
      symbol_table)
      .symbol_expr();

  // Generate "address of write set" variable
  const auto &addr_of_write_set_var =
    get_fresh_aux_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET_PTR],
      id2string(function_id),
      "__address_of_write_set_loop_" + std::to_string(cbmc_loop_number),
      loop.head->source_location(),
      language_mode,
      symbol_table)
      .symbol_expr();

  return {
    loop_id,
    cbmc_loop_number,
    contract_clauses.assigns,
    contract_clauses.invariant_expr,
    contract_clauses.decreases_clauses,
    loop_locals,
    loop_tracked,
    inner_loops,
    outer_loops,
    write_set_var,
    addr_of_write_set_var};
}

dfcc_cfg_infot::dfcc_cfg_infot(
  const irep_idt &function_id,
  goto_functiont &goto_function,
  const exprt &top_level_write_set,
  const dfcc_loop_contract_modet loop_contract_mode,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library)
  : function_id(function_id),
    goto_function(goto_function),
    top_level_write_set(top_level_write_set),
    log(message_handler),
    ns(symbol_table)
{
  dfcc_loop_nesting_grapht loop_nesting_graph;
  goto_programt &goto_program = goto_function.body;
  messaget log(message_handler);
  if(loop_contract_mode != dfcc_loop_contract_modet::NONE)
  {
    dfcc_check_loop_normal_form(goto_program, log);
    loop_nesting_graph = build_loop_nesting_graph(goto_program, log);

    const auto head = check_inner_loops_have_contracts(loop_nesting_graph);
    if(head.has_value())
    {
      throw invalid_source_file_exceptiont(
        "Found loop without contract nested in a loop with a "
        "contract.\nPlease "
        "provide a contract or unwind this loop before applying loop "
        "contracts.",
        head.value()->source_location());
    }

    auto topsorted = loop_nesting_graph.topsort();

    for(const auto idx : topsorted)
    {
      topsorted_loops.push_back(idx);
    }
  }

  // At this point, either loop contracts were activated and the loop nesting
  // graph describes the loop structure of the function,
  // or loop contracts were not activated and the loop nesting graph is empty
  // (i.e. there might be some loops in the function but we won't consider them
  // for the instrumentation).
  // In both cases, we tag program instructions and generate the dfcc_cfg_infot
  // instance from that graph's contents. The tags will decide against which
  // write set the instructions are going to be instrumented (either the
  // function's write set, or the write set of a loop), and each dfcc_loop_infot
  // contained in the loop_info_map describes a loop to be abstracted by a
  // contract.

  tag_loop_instructions(goto_program, loop_nesting_graph);

  // generate dfcc_cfg_loop_info for loops and add to loop_info_map
  dirtyt dirty(goto_function);
  local_may_aliast local_may_alias(goto_function);

  for(const auto &loop_id : topsorted_loops)
  {
    loop_info_map.insert(
      {loop_id,
       gen_dfcc_loop_info(
         loop_nesting_graph,
         loop_id,
         function_id,
         loop_info_map,
         dirty,
         local_may_alias,
         message_handler,
         utils,
         library,
         symbol_table)});

    if(loop_nesting_graph.get_successors(loop_id).empty())
      top_level_loops.push_back(loop_id);
  }

  // generate set of top level of locals
  top_level_local.insert(
    goto_function.parameter_identifiers.begin(),
    goto_function.parameter_identifiers.end());

  for(auto target = goto_function.body.instructions.begin();
      target != goto_function.body.instructions.end();
      target++)
  {
    if(target->is_decl() && dfcc_is_loop_top_level(target))
      top_level_local.insert(target->decl_symbol().get_identifier());
  }

  top_level_tracked =
    gen_tracked_set(top_level_loops, top_level_local, dirty, loop_info_map);
}

void dfcc_cfg_infot::output(std::ostream &out) const
{
  out << "// dfcc_cfg_infot for:  " << function_id << "\n";
  out << "// top_level_local: {";
  for(auto &id : top_level_local)
  {
    out << id << ", ";
  }
  out << "}\n";

  out << "// top_level_tracked: {";
  for(auto &id : top_level_tracked)
  {
    out << id << ", ";
  }
  out << "}\n";

  out << "// loop:\n";
  for(auto &loop : loop_info_map)
  {
    out << "// dfcc-loop_id:" << loop.first << "\n";
    auto head = loop.second.find_head(goto_function.body);
    auto latch = loop.second.find_latch(goto_function.body);
    out << "// head:\n";
    head.value()->output(out);
    out << "// latch:\n";
    latch.value()->output(out);
    loop.second.output(out);
  }
  out << "// program:\n";
  Forall_goto_program_instructions(target, goto_function.body)
  {
    out << "// dfcc-loop-id:" << dfcc_get_loop_id(target).value();
    out << " cbmc-loop-number:" << target->loop_number;
    out << " top-level:" << dfcc_is_loop_top_level(target);
    out << " head:" << dfcc_is_loop_head(target);
    out << " body:" << dfcc_is_loop_body(target);
    out << " exiting:" << dfcc_is_loop_exiting(target);
    out << " latch:" << dfcc_is_loop_latch(target);
    out << "\n";
    target->output(out);
  }
}

const exprt &
dfcc_cfg_infot::get_write_set(goto_programt::const_targett target) const
{
  auto loop_id_opt = dfcc_get_loop_id(target);
  PRECONDITION(
    loop_id_opt.has_value() &&
    is_valid_loop_or_top_level_id(loop_id_opt.value()));
  auto loop_id = loop_id_opt.value();
  if(is_top_level_id(loop_id))
  {
    return top_level_write_set;
  }
  else
  {
    return loop_info_map.at(loop_id).addr_of_write_set_var;
  }
}

const std::unordered_set<irep_idt> &
dfcc_cfg_infot::get_tracked_set(goto_programt::const_targett target) const
{
  auto loop_id_opt = dfcc_get_loop_id(target);
  PRECONDITION(
    loop_id_opt.has_value() &&
    is_valid_loop_or_top_level_id(loop_id_opt.value()));
  auto loop_id = loop_id_opt.value();
  if(is_top_level_id(loop_id))
  {
    return top_level_tracked;
  }
  else
  {
    return loop_info_map.at(loop_id).tracked;
  }
}

const std::unordered_set<irep_idt> &
dfcc_cfg_infot::get_local_set(goto_programt::const_targett target) const
{
  auto loop_id_opt = dfcc_get_loop_id(target);
  PRECONDITION(
    loop_id_opt.has_value() &&
    is_valid_loop_or_top_level_id(loop_id_opt.value()));
  auto loop_id = loop_id_opt.value();
  if(is_top_level_id(loop_id))
  {
    return top_level_local;
  }
  else
  {
    return loop_info_map.at(loop_id).local;
  }
}

const exprt &dfcc_cfg_infot::get_outer_write_set(std::size_t loop_id) const
{
  PRECONDITION(is_valid_loop_id(loop_id));
  auto outer_loop_opt = get_outer_loop_identifier(loop_id);
  return outer_loop_opt.has_value()
           ? get_loop_info(outer_loop_opt.value()).addr_of_write_set_var
           : top_level_write_set;
}

const dfcc_loop_infot &
dfcc_cfg_infot::get_loop_info(const std::size_t loop_id) const
{
  return loop_info_map.at(loop_id);
}

// find the identifier or the immediately enclosing loop in topological order
const optionalt<std::size_t>
dfcc_cfg_infot::get_outer_loop_identifier(const std::size_t loop_id) const
{
  PRECONDITION(is_valid_loop_id(loop_id));
  auto outer_loops = get_loop_info(loop_id).outer_loops;

  // find the first loop in the topological order that is connected
  // to our node.
  for(const auto &idx : get_loops_toposorted())
  {
    if(
      std::find(outer_loops.begin(), outer_loops.end(), idx) !=
      outer_loops.end())
    {
      return idx;
    }
  }
  // return nullopt for loops that are not nested in other loops
  return nullopt;
}

bool dfcc_cfg_infot::is_valid_loop_or_top_level_id(const std::size_t id) const
{
  return id <= loop_info_map.size();
}

bool dfcc_cfg_infot::is_valid_loop_id(const std::size_t id) const
{
  return id < loop_info_map.size();
}

bool dfcc_cfg_infot::is_top_level_id(const std::size_t id) const
{
  return id == loop_info_map.size();
}

bool dfcc_cfg_infot::must_track_decl_or_dead(
  goto_programt::const_targett target) const
{
  PRECONDITION(target->is_decl() || target->is_dead());
  auto &ident = target->is_decl() ? target->decl_symbol().get_identifier()
                                  : target->dead_symbol().get_identifier();
  auto &tracked = get_tracked_set(target);
  return tracked.find(ident) != tracked.end();
}
#include <iostream>

/// Returns true if the lhs to an assignment must be checked against its write
/// set. The set of locally declared identifiers and the subset of that that
/// are tracked explicitly in the write set are used to make the decision.
/// See comments inside the function for explanations.
static bool must_check_lhs_from_local_and_tracked(
  const exprt &lhs,
  const std::unordered_set<irep_idt> &local,
  const std::unordered_set<irep_idt> &tracked)
{
  auto root_objects = dfcc_root_objects(lhs);

  // Check wether all root_objects can be resolved to actual identifiers.
  std::unordered_set<irep_idt> root_idents;
  for(const auto &expr : root_objects)
  {
    if(expr.id() != ID_symbol)
    {
      // This means that lhs contains either an address-of operation or a
      // dereference operation, and we cannot really know statically which
      // object it refers to without using the may_alias analysis.
      // Since the may_alias analysis is also used to infer targets, for
      // soundness reasons we cannot also use it to skip checks, so we check
      // the assignment. If happens to assign to a mix of tracked and
      // non-tracked identifiers the check will fail but this is sound anyway.
      return true;
    }
    const auto &id = to_symbol_expr(expr).get_identifier();
    if(dfcc_is_cprover_symbol(id))
    {
      // Skip the check if we have a single cprover symbol as root object
      // cprover symbols are used for generic checks instrumentation and are
      // de-facto ghost code. We implicitly allow assignments to these symbols.
      // To make this really sound we should use a white list of known
      // CPROVER symbols, because right now simply naming a symbol with the
      // CPROVER prefix bypasses the checks.
      if(root_objects.size() == 1)
      {
        return false;
      }
      else
      {
        // error out if we have a cprover symbol and something else in the set
        throw analysis_exceptiont(
          "LHS expression `" + format_to_string(lhs) +
          "` in assignment refers to a cprover symbol and something else.");
      }
    }
    root_idents.insert(id);
  }

  // The root idents set is Non-empty.
  // true iff root_idents contains non-local idents
  bool some_non_local = false;
  // true iff root_idents contains some local that is not tracked
  bool some_local_not_tracked = false;
  // true iff root_idents contains only local that are not tracked
  bool all_local_not_tracked = true;
  // true iff root_idents contains only local that are tracked
  bool all_local_tracked = true;
  for(const auto &root_ident : root_idents)
  {
    bool loc = local.find(root_ident) != local.end();
    bool tra = tracked.find(root_ident) != tracked.end();
    bool local_tracked = loc && tra;
    bool local_not_tracked = loc && !tra;
    some_non_local |= !loc;
    some_local_not_tracked |= local_not_tracked;
    all_local_not_tracked &= local_not_tracked;
    all_local_tracked &= local_tracked;
  }

  // some root identifier is not local, the lhs must be checked
  if(some_non_local)
  {
    // if we also have a local that is not tracked, we know the check will
    // fail with the current algorithm, error out.
    if(some_local_not_tracked)
    {
      throw analysis_exceptiont(
        "LHS expression `" + format_to_string(lhs) +
        "` in assignment mentions both explicitly and implicitly tracked "
        "memory locations. DFCC does not yet handle that case, please "
        "reformulate the assignment into separate assignments to either "
        "memory locations.");
    }
    return true;
  }
  else
  {
    // all root identifiers are local
    // if they are all not tracked, we *have* to skip the check
    // (and it is sound to do so, because we know that the identifiers that
    // are not tracked explicitly are not dirty and not assigned to outside of
    // their scope).
    // if they are all tracked, we *can* skip the check, because they are all
    // local to that scope anyway and implicitly allowed.
    if(all_local_not_tracked || all_local_tracked)
    {
      return false;
    }
    else
    {
      // we have a combination of tracked and not-tracked locals, we know
      // the check will fail with the current algorithm, error out.
      throw analysis_exceptiont(
        "LHS expression `" + format_to_string(lhs) +
        "` in assignment mentions both explicitly and implicitly tracked "
        "memory locations. DFCC does not yet handle that case, please "
        "reformulate the assignment into separate assignments to either "
        "memory locations.");
    }
  }
}

bool dfcc_cfg_infot::must_check_lhs(goto_programt::const_targett target) const
{
  PRECONDITION(target->is_assign() || target->is_function_call());
  const exprt &lhs =
    target->is_assign() ? target->assign_lhs() : target->call_lhs();
  if(lhs.is_nil())
    return false;
  return must_check_lhs_from_local_and_tracked(
    lhs, get_local_set(target), get_tracked_set(target));
}
