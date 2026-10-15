/*******************************************************************\

Module: If-conversion of side-effect-free conditional assignments

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// If-conversion of side-effect-free conditional assignments

#include "if_conversion.h"

#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "goto_model.h"
#include "remove_skip.h"

#include <map>
#include <set>
#include <vector>

/// An instruction may appear in a region that we linearise iff it neither
/// transfers control nor has effects beyond a plain assignment or a scope
/// marker. In particular function calls, assertions/assumptions, atomic
/// sections and (non-structural) jumps are excluded: linearising them would
/// be unsound or change semantics. DECL/DEAD are permitted (they only widen
/// the scope of branch-local variables, which is harmless once the guard has
/// been snapshotted).
///
/// In addition, an assignment whose left-hand side contains a dereference or
/// an array index is excluded: linearising `if(c) *p = v;` into
/// `*p = c ? v : *p` (or `a[i] = c ? v : a[i]`) would evaluate the address
/// `*p` / `a[i]` unconditionally, performing the dereference or array-bounds
/// access even when the guard does not hold. That both changes semantics and
/// defeats the precision the guard provided (null/bounds safety).
static bool
is_region_instruction(const goto_programt::instructiont &instruction)
{
  if(instruction.is_assign())
  {
    const exprt &lhs = instruction.assign_lhs();
    return !has_subexpr(lhs, ID_dereference) && !has_subexpr(lhs, ID_index);
  }

  return instruction.is_skip() || instruction.is_decl() ||
         instruction.is_dead();
}

namespace
{
/// Create a fresh static boolean to hold a snapshot of a branch condition.
/// A static lifetime avoids the need for DECL/DEAD bookkeeping; the variable
/// is always assigned immediately before it is read, so its (uninitialised)
/// global value is never observed.
symbol_exprt fresh_guard_symbol(
  symbol_table_baset &symbol_table,
  const irep_idt &mode,
  const source_locationt &source_location,
  std::size_t &counter)
{
  irep_idt base_name = "if_conversion_guard$" + std::to_string(counter++);
  irep_idt name = CPROVER_PREFIX + id2string(base_name);

  symbolt symbol{name, bool_typet{}, mode};
  symbol.base_name = base_name;
  symbol.pretty_name = base_name;
  symbol.is_static_lifetime = true;
  symbol.is_lvalue = true;
  symbol.is_state_var = true;
  symbol.is_file_local = true;
  symbol.location = source_location;

  symbol_table.insert(std::move(symbol));

  return symbol_exprt{name, bool_typet{}};
}
} // namespace

std::size_t if_conversion(
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  const irep_idt &mode,
  const namespacet &ns)
{
  // Map each instruction to the set of instructions that jump to it, so that
  // we can ensure that the branch we remove is the only way into the region we
  // linearise (and that the branch itself is not a jump target). Built once;
  // it is treated conservatively (a stale entry only prevents a later
  // conversion, it never enables an unsound one).
  std::map<
    const goto_programt::instructiont *,
    std::set<const goto_programt::instructiont *>>
    incoming;
  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it)
  {
    for(const auto &t : it->targets)
      incoming[&*t].insert(&*it);
  }

  const auto externally_entered =
    [&incoming](
      goto_programt::targett p,
      const goto_programt::instructiont *branch,
      const goto_programt::instructiont *structural)
  {
    const auto m = incoming.find(&*p);
    if(m == incoming.end())
      return false;
    for(const auto *src : m->second)
      if(src != branch && src != structural)
        return true;
    return false;
  };

  std::size_t converted = 0;
  std::size_t guard_counter = 0;

  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it)
  {
    // candidate: a conditional GOTO with a single, forward target
    if(!it->is_goto() || it->targets.size() != 1)
      continue;

    const exprt guard = it->condition();
    if(guard.is_true() || guard.is_false())
      continue;

    // the branch itself must not be a jump target, so that the guard snapshot
    // we insert just before it is reached on every entry
    if(incoming.find(&*it) != incoming.end())
      continue;

    const goto_programt::targett target = it->get_target();

    // the then-region is [then_begin, target); require target to be reachable
    // forwards (otherwise this is a back-edge / loop)
    const goto_programt::targett then_begin = std::next(it);
    std::vector<goto_programt::targett> region1;
    bool forward = false;
    for(auto p = then_begin; p != goto_program.instructions.end(); ++p)
    {
      if(p == target)
      {
        forward = true;
        break;
      }
      region1.push_back(p);
    }
    if(!forward)
      continue;

    // if-else shape: the then-region ends in an unconditional forward GOTO
    // whose target (the join) lies beyond the else-entry `target`
    goto_programt::targett structural_goto = goto_program.instructions.end();
    std::vector<goto_programt::targett> region2;
    bool is_if_else = false;
    if(
      !region1.empty() && region1.back()->is_goto() &&
      region1.back()->condition().is_true() &&
      region1.back()->targets.size() == 1)
    {
      const goto_programt::targett join = region1.back()->get_target();
      bool join_forward = false;
      for(auto p = target; p != goto_program.instructions.end(); ++p)
      {
        if(p == join)
        {
          join_forward = true;
          break;
        }
      }
      if(join_forward && join != target)
      {
        structural_goto = region1.back();
        region1.pop_back();
        is_if_else = true;
        for(auto p = target; p != join; ++p)
          region2.push_back(p);
      }
    }

    // both regions must consist of linearisable instructions only
    const auto linearisable =
      [](const std::vector<goto_programt::targett> &region)
    {
      for(const auto &p : region)
        if(!is_region_instruction(*p))
          return false;
      return true;
    };
    if(!linearisable(region1) || !linearisable(region2))
      continue;

    // at least one region must contain an assignment, otherwise there is
    // nothing worth linearising
    const auto has_assignment =
      [](const std::vector<goto_programt::targett> &region)
    {
      for(const auto &p : region)
        if(p->is_assign())
          return true;
      return false;
    };
    if(!has_assignment(region1) && !has_assignment(region2))
      continue;

    // single-entry: no instruction in the region(s), nor the else-entry, may
    // be the target of any jump other than the branch (and the structural
    // GOTO) we are removing
    const goto_programt::instructiont *const structural_ptr =
      is_if_else ? &*structural_goto : nullptr;
    bool external_entry = false;
    for(const auto &p : region1)
      external_entry |= externally_entered(p, &*it, structural_ptr);
    for(const auto &p : region2)
      external_entry |= externally_entered(p, &*it, structural_ptr);
    if(is_if_else)
      external_entry |= externally_entered(target, &*it, structural_ptr);
    if(external_entry)
      continue;

    // Snapshotting the guard into a fresh variable is necessary when the guard
    // reads a variable that the region writes or kills: otherwise re-evaluating
    // the guard at each converted assignment could observe a clobbered value,
    // or read a now-DEAD condition temporary. When the guard does not depend on
    // anything the region touches we can use the original condition directly,
    // which keeps the conditional assignments analysable downstream (e.g. it
    // preserves `p != null` guards for local safe pointer analysis).
    const find_symbols_sett guard_symbols = find_symbol_identifiers(guard);
    bool guard_depends_on_region = false;
    const auto note_region_writes = [&guard_symbols, &guard_depends_on_region](
                                      const goto_programt::targett &p)
    {
      if(p->is_assign())
      {
        for(const irep_idt &id : find_symbol_identifiers(p->assign_lhs()))
          if(guard_symbols.count(id) != 0)
            guard_depends_on_region = true;
      }
      else if(p->is_decl())
      {
        if(guard_symbols.count(p->decl_symbol().get_identifier()) != 0)
          guard_depends_on_region = true;
      }
      else if(p->is_dead())
      {
        if(guard_symbols.count(p->dead_symbol().get_identifier()) != 0)
          guard_depends_on_region = true;
      }
    };
    for(const auto &p : region1)
      note_region_writes(p);
    for(const auto &p : region2)
      note_region_writes(p);

    // For an if/else, the else-region is linearised after the then-region, so
    // converting each region independently into a self-referential conditional
    // assignment `x = c ? e : x` makes an else-assignment that reads a variable
    // the then-region wrote nest (after SSA) into `x = !c ? b : (c ? a : x)`.
    // That defeats constant propagation of `x`: a variable that was concrete on
    // each original branch becomes a symbolic value, and in --paths mode that
    // can drive downstream branches/loops into an explosion of paths (see
    // regression/cbmc/return4). When both regions are a single assignment to
    // the same variable we instead emit one combined ternary `x = c ? a : b`,
    // which simplify can fold (e.g. `c ? 1 : 1` to `1`); messier overlaps are
    // left unconverted. Regions that do not interfere keep the per-region form.
    goto_programt::targett combine_then = goto_program.instructions.end();
    goto_programt::targett combine_else = goto_program.instructions.end();
    bool combine = false;
    if(is_if_else)
    {
      find_symbols_sett region1_writes;
      for(const auto &p : region1)
      {
        if(p->is_assign())
        {
          for(const irep_idt &id : find_symbol_identifiers(p->assign_lhs()))
            region1_writes.insert(id);
        }
        else if(p->is_decl())
          region1_writes.insert(p->decl_symbol().get_identifier());
      }

      bool region2_uses_region1_write = false;
      std::vector<goto_programt::targett> region1_assignments;
      std::vector<goto_programt::targett> region2_assignments;
      for(const auto &p : region1)
        if(p->is_assign())
          region1_assignments.push_back(p);
      for(const auto &p : region2)
      {
        if(p->is_assign())
        {
          region2_assignments.push_back(p);
          for(const irep_idt &id : find_symbol_identifiers(p->assign_lhs()))
            if(region1_writes.count(id) != 0)
              region2_uses_region1_write = true;
          for(const irep_idt &id : find_symbol_identifiers(p->assign_rhs()))
            if(region1_writes.count(id) != 0)
              region2_uses_region1_write = true;
        }
        else if(
          p->is_decl() &&
          region1_writes.count(p->decl_symbol().get_identifier()) != 0)
          region2_uses_region1_write = true;
        else if(
          p->is_dead() &&
          region1_writes.count(p->dead_symbol().get_identifier()) != 0)
          region2_uses_region1_write = true;
      }

      if(region2_uses_region1_write)
      {
        if(
          region1_assignments.size() == 1 && region2_assignments.size() == 1 &&
          region1_assignments.front()->assign_lhs() ==
            region2_assignments.front()->assign_lhs())
        {
          combine = true;
          combine_then = region1_assignments.front();
          combine_else = region2_assignments.front();
        }
        else
          continue; // leave the branch in place rather than create a chain
      }
    }

    // the then-region executes when the GOTO is *not* taken, the else-region
    // when it is taken
    exprt then_condition;
    exprt else_condition;
    if(guard_depends_on_region)
    {
      const symbol_exprt snapshot = fresh_guard_symbol(
        symbol_table, mode, it->source_location(), guard_counter);
      goto_program.insert_before(
        it,
        goto_programt::make_assignment(snapshot, guard, it->source_location()));
      then_condition = boolean_negate(snapshot);
      else_condition = snapshot;
    }
    else
    {
      then_condition = boolean_negate(guard);
      else_condition = guard;
    }
    simplify(then_condition, ns);

    if(combine)
    {
      // x = c ? then_rhs : else_rhs, replacing the matching assignment pair;
      // the else-assignment becomes a skip
      exprt combined = if_exprt{
        then_condition, combine_then->assign_rhs(), combine_else->assign_rhs()};
      simplify(combined, ns);
      combine_then->assign_rhs_nonconst() = std::move(combined);
      *combine_else = goto_programt::make_skip(combine_else->source_location());
    }
    else
    {
      for(const auto &p : region1)
      {
        if(!p->is_assign())
          continue;
        const exprt lhs = p->assign_lhs();
        const exprt rhs = p->assign_rhs();
        p->assign_rhs_nonconst() = if_exprt{then_condition, rhs, lhs};
      }
      for(const auto &p : region2)
      {
        if(!p->is_assign())
          continue;
        const exprt lhs = p->assign_lhs();
        const exprt rhs = p->assign_rhs();
        p->assign_rhs_nonconst() = if_exprt{else_condition, rhs, lhs};
      }
    }

    // drop the branch(es)
    *it = goto_programt::make_skip(it->source_location());
    if(is_if_else)
      *structural_goto =
        goto_programt::make_skip(structural_goto->source_location());

    ++converted;
  }

  return converted;
}

std::size_t
if_conversion(goto_modelt &goto_model, message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::size_t converted = 0;

  for(auto &gf : goto_model.goto_functions.function_map)
  {
    const symbolt *fn = goto_model.symbol_table.lookup(gf.first);
    const irep_idt mode = fn != nullptr ? fn->mode : ID_C;
    converted +=
      if_conversion(gf.second.body, goto_model.symbol_table, mode, ns);
  }

  if(converted != 0)
  {
    remove_skip(goto_model);
    goto_model.goto_functions.update();

    messaget log(message_handler);
    log.statistics() << "if-conversion replaced " << converted
                     << " branch(es) with conditional assignments"
                     << messaget::eom;
  }

  return converted;
}
