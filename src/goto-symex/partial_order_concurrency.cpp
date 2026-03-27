/*******************************************************************\

Module: Add constraints to equation encoding partial orders on events

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Add constraints to equation encoding partial orders on events

#include "partial_order_concurrency.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/symbol.h>

partial_order_concurrencyt::partial_order_concurrencyt(const namespacet &_ns)
  : ns(_ns)
{
}

partial_order_concurrencyt::~partial_order_concurrencyt()
{
}

void partial_order_concurrencyt::add_init_writes(
  symex_target_equationt &equation)
{
  std::unordered_set<irep_idt> init_done;
  bool spawn_seen = false;

  symex_target_equationt::SSA_stepst init_steps;

  for(eventst::const_iterator e_it = equation.SSA_steps.begin();
      e_it != equation.SSA_steps.end();
      e_it++)
  {
    if(e_it->is_spawn())
    {
      spawn_seen = true;
      continue;
    }
    else if(!e_it->is_shared_read() && !e_it->is_shared_write())
      continue;

    const irep_idt &a = address(e_it);

    if(init_done.find(a) != init_done.end())
      continue;

    // Skip may-alias addresses -- their initialization is handled through
    // the aliasing constraints in the memory model, not through init writes.
    const irep_idt &obj_name = e_it->ssa_lhs.get_object_name();
    if(id2string(obj_name).find("concurrency::may_alias") != std::string::npos)
    {
      init_done.insert(a);
      continue;
    }

    if(spawn_seen || e_it->is_shared_read() || e_it->guard != true)
    {
      init_steps.emplace_back(
        e_it->source, goto_trace_stept::typet::SHARED_WRITE);
      SSA_stept &SSA_step = init_steps.back();

      SSA_step.guard = true_exprt();
      // no SSA L2 index, thus nondet value
      SSA_step.ssa_lhs = remove_level_2(e_it->ssa_lhs);
      SSA_step.atomic_section_id = 0;
    }

    init_done.insert(a);
  }

  equation.SSA_steps.splice(equation.SSA_steps.begin(), init_steps);
}

void partial_order_concurrencyt::build_event_lists(
  symex_target_equationt &equation,
  message_handlert &message_handler)
{
  add_init_writes(equation);

  // a per-thread counter
  std::map<unsigned, unsigned> counter;

  for(eventst::const_iterator e_it = equation.SSA_steps.begin();
      e_it != equation.SSA_steps.end();
      e_it++)
  {
    if(e_it->is_shared_read() || e_it->is_shared_write() || e_it->is_spawn())
    {
      unsigned thread_nr = e_it->source.thread_nr;

      if(!e_it->is_spawn())
      {
        const irep_idt &addr = address(e_it);
        a_rect &a_rec = address_map[addr];

        if(e_it->is_shared_read())
          a_rec.reads.push_back(e_it);
        else // must be write
          a_rec.writes.push_back(e_it);

        // Record a representative L1 symbol for non-may-alias addresses
        const irep_idt &obj_name = e_it->ssa_lhs.get_object_name();
        if(
          id2string(obj_name).find("concurrency::may_alias") ==
            std::string::npos &&
          address_representatives.find(addr) == address_representatives.end())
        {
          address_representatives.emplace(addr, remove_level_2(e_it->ssa_lhs));
        }
      }

      // maps an event id to a per-thread counter
      unsigned cnt = counter[thread_nr]++;
      numbering[e_it] = cnt;
    }
  }

  // Second pass: for each may-alias event, add it to all non-may-alias
  // addresses' read/write lists so it participates in their constraints.
  // Only add to addresses where the base type is compatible.
  for(eventst::const_iterator e_it = equation.SSA_steps.begin();
      e_it != equation.SSA_steps.end();
      e_it++)
  {
    if(!e_it->is_shared_read() && !e_it->is_shared_write())
      continue;

    const irep_idt &obj_name = e_it->ssa_lhs.get_object_name();
    if(id2string(obj_name).find("concurrency::may_alias") == std::string::npos)
      continue;

    const typet &may_alias_type = e_it->ssa_lhs.type();

    // This is a may-alias event -- add it to all other non-may-alias addresses
    for(auto &addr_entry : address_map)
    {
      // Skip the may-alias object's own address entry
      if(addr_entry.first == address(e_it))
        continue;

      // Skip other may-alias addresses
      if(
        id2string(addr_entry.first).find("concurrency::may_alias") !=
        std::string::npos)
        continue;

      // Only add to addresses with matching type to avoid type mismatches
      // in value equality constraints
      auto rep_it = address_representatives.find(addr_entry.first);
      if(rep_it == address_representatives.end())
        continue;
      if(rep_it->second.type() != may_alias_type)
        continue;

      if(e_it->is_shared_read())
        addr_entry.second.reads.push_back(e_it);
      else
        addr_entry.second.writes.push_back(e_it);
    }
  }

  messaget log{message_handler};
  for(address_mapt::const_iterator a_it = address_map.begin();
      a_it != address_map.end();
      a_it++)
  {
    const a_rect &a_rec = a_it->second;
    if(a_rec.reads.empty())
      continue;

    log.statistics() << "Shared " << a_it->first << ": " << a_rec.reads.size()
                     << "R/" << a_rec.writes.size() << "W" << messaget::eom;
  }
}

irep_idt partial_order_concurrencyt::rw_clock_id(event_it event, axiomt axiom)
{
  if(event->is_shared_write())
    return id2string(id(event)) + "$wclk$" + std::to_string(axiom);
  else if(event->is_shared_read())
    return id2string(id(event)) + "$rclk$" + std::to_string(axiom);
  else
    UNREACHABLE;
}

symbol_exprt partial_order_concurrencyt::clock(event_it event, axiomt axiom)
{
  PRECONDITION(!numbering.empty());
  irep_idt identifier;

  if(event->is_shared_write())
    identifier = rw_clock_id(event, axiom);
  else if(event->is_shared_read())
    identifier = rw_clock_id(event, axiom);
  else if(event->is_spawn())
  {
    identifier = "t" + std::to_string(event->source.thread_nr + 1) + "$" +
                 std::to_string(numbering[event]) + "$spwnclk$" +
                 std::to_string(axiom);
  }
  else
    UNREACHABLE;

  return symbol_exprt(identifier, clock_type);
}

void partial_order_concurrencyt::build_clock_type()
{
  PRECONDITION(!numbering.empty());

  std::size_t width = address_bits(numbering.size());
  clock_type = unsignedbv_typet(width);
}

exprt partial_order_concurrencyt::before(
  event_it e1,
  event_it e2,
  unsigned axioms)
{
  const axiomt axiom_bits[] = {
    AX_SC_PER_LOCATION, AX_NO_THINAIR, AX_OBSERVATION, AX_PROPAGATION};

  exprt::operandst ops;
  ops.reserve(sizeof(axiom_bits) / sizeof(axiomt));

  for(int i = 0; i < int(sizeof(axiom_bits) / sizeof(axiomt)); ++i)
  {
    const axiomt ax = axiom_bits[i];

    if((axioms & ax) == 0)
      continue;

    if(
      e1->atomic_section_id != 0 &&
      e1->atomic_section_id == e2->atomic_section_id)
      ops.push_back(equal_exprt(clock(e1, ax), clock(e2, ax)));
    else
      ops.push_back(binary_relation_exprt(clock(e1, ax), ID_lt, clock(e2, ax)));
  }

  POSTCONDITION(!ops.empty());

  return conjunction(ops);
}

void partial_order_concurrencyt::add_constraint(
  symex_target_equationt &equation,
  const exprt &cond,
  const std::string &msg,
  const symex_targett::sourcet &source) const
{
  exprt tmp = cond;
  simplify(tmp, ns);

  equation.constraint(tmp, msg, source);
}

exprt partial_order_concurrencyt::alias_condition(
  event_it event,
  const irep_idt &target_address) const
{
  const irep_idt &obj_name = event->ssa_lhs.get_object_name();
  if(id2string(obj_name).find("concurrency::may_alias") == std::string::npos)
    return true_exprt{};

  // Look up the source pointer from the symbol table via the object name
  const symbolt *sym_ptr;
  if(ns.lookup(obj_name, sym_ptr) || sym_ptr->value.is_nil())
    return true_exprt{};

  const exprt &source_pointer = sym_ptr->value;

  // Find a representative non-may-alias event at the target address to build
  // the address-of expression for comparison.
  auto rep_it = address_representatives.find(target_address);
  if(rep_it == address_representatives.end())
    return true_exprt{};

  const ssa_exprt &target_l1_sym = rep_it->second;

  // Build: pointer_object(source_pointer) == pointer_object(&target)
  const typet po_type = unsignedbv_typet{config.bv_encoding.object_bits};

  address_of_exprt target_addr(target_l1_sym);

  return equal_exprt{
    pointer_object_exprt{source_pointer, po_type},
    pointer_object_exprt{target_addr, po_type}};
}
