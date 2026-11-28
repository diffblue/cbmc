/*******************************************************************\

Module: Partial-order reduction for --evaluation-order-check

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Partial-order reduction for --evaluation-order-check

#include "evaluation_order_reduction.h"

#include <util/byte_operators.h>
#include <util/expr_util.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

#include <pointer-analysis/value_set_analysis_fi.h>

#include <map>
#include <set>
#include <unordered_map>
#include <vector>

namespace
{
/// The memory objects that code may read and write.
struct footprintt
{
  std::set<irep_idt> reads;
  std::set<irep_idt> writes;
  /// Set when the code may access memory that is not known.
  bool unknown = false;

  /// Add \p other to this footprint. \return true if this footprint changed
  bool add(const footprintt &other)
  {
    const std::size_t old_size = reads.size() + writes.size();
    const bool old_unknown = unknown;
    reads.insert(other.reads.begin(), other.reads.end());
    writes.insert(other.writes.begin(), other.writes.end());
    unknown = unknown || other.unknown;
    return unknown != old_unknown || reads.size() + writes.size() != old_size;
  }

  /// Returns true if executing code with this footprint and code with the
  /// \p other footprint in either order may yield different results.
  bool conflicts_with(const footprintt &other) const
  {
    if(unknown || other.unknown)
      return true;
    return intersect(writes, other.reads) || intersect(writes, other.writes) ||
           intersect(reads, other.writes);
  }

  /// Returns true if code with this footprint may change the value of an
  /// expression that reads the memory in \p read.
  bool may_change(const footprintt &read) const
  {
    return unknown || read.unknown || intersect(writes, read.reads);
  }

private:
  static bool
  intersect(const std::set<irep_idt> &a, const std::set<irep_idt> &b)
  {
    for(const auto &id : a)
    {
      if(b.find(id) != b.end())
        return true;
    }
    return false;
  }
};

/// Computes the footprints of instructions, of instruction ranges, and of
/// functions including the functions they call.
class footprint_collectort
{
public:
  footprint_collectort(
    const goto_modelt &goto_model,
    value_set_analysis_fit &value_sets)
    : goto_model(goto_model),
      ns(goto_model.symbol_table),
      value_sets(value_sets)
  {
  }

  /// Add the footprint of \p target in \p function to \p dest, including the
  /// footprint of any function it calls.
  void add_instruction(
    const irep_idt &function,
    goto_programt::const_targett target,
    footprintt &dest)
  {
    std::set<irep_idt> callees;
    add_local(function, target, {}, dest, callees);
    for(const auto &callee : callees)
      dest.add(summary(callee));
  }

private:
  const goto_modelt &goto_model;
  const namespacet ns;
  value_set_analysis_fit &value_sets;

  struct function_infot
  {
    footprintt local;
    std::set<irep_idt> callees;
  };
  std::unordered_map<irep_idt, function_infot> function_infos;
  std::unordered_map<irep_idt, footprintt> summaries;

  /// State of the instruction currently being analysed.
  irep_idt function;
  goto_programt::const_targett target;
  irep_idt excluded_locals;
  footprintt *footprint = nullptr;

  /// Returns true if \p identifier is a parameter or a local variable of the
  /// function whose summary is being computed: each call has its own
  /// instance of such an object, and pointers to it do not outlive the call.
  bool is_excluded(const irep_idt &identifier) const
  {
    if(
      excluded_locals.empty() ||
      !has_prefix(id2string(identifier), id2string(excluded_locals) + "::"))
    {
      return false;
    }
    const symbolt *symbol = ns.get_symbol_table().lookup(identifier);
    return symbol != nullptr && !symbol->is_static_lifetime;
  }

  void add_pointees(const exprt &pointer, std::set<irep_idt> &dest)
  {
    const std::vector<exprt> values =
      value_sets.get_values(function, target, pointer);
    // A pointer that is never assigned, such as a nondeterministic argument
    // of the entry point, may point anywhere.
    if(values.empty())
      footprint->unknown = true;
    for(const exprt &value : values)
    {
      if(value.id() != ID_object_descriptor)
      {
        footprint->unknown = true;
        continue;
      }
      const exprt &root = to_object_descriptor_expr(value).root_object();
      if(root.id() == ID_symbol)
        dest.insert(to_symbol_expr(root).identifier());
      else if(root.id() == ID_dynamic_object)
      {
        dest.insert(
          "dynamic_object$" +
          std::to_string(to_dynamic_object_expr(root).get_instance()));
      }
      else if(root.id() == ID_string_constant)
        dest.insert(ID_string_constant);
      else if(root.id() != ID_null_object)
        footprint->unknown = true;
    }
  }

  void add_read(const exprt &expr)
  {
    if(expr.id() == ID_symbol)
    {
      const irep_idt &identifier = to_symbol_expr(expr).identifier();
      if(expr.type().id() != ID_code && !is_excluded(identifier))
        footprint->reads.insert(identifier);
    }
    else if(expr.id() == ID_dereference)
    {
      const exprt &pointer = to_dereference_expr(expr).pointer();
      add_read(pointer);
      add_pointees(pointer, footprint->reads);
    }
    else if(expr.id() == ID_address_of)
      add_address(to_address_of_expr(expr).object());
    else
    {
      for(const auto &op : expr.operands())
        add_read(op);
    }
  }

  /// Add the reads needed to compute the address of \p object.
  void add_address(const exprt &object)
  {
    if(object.id() == ID_index)
    {
      add_address(to_index_expr(object).array());
      add_read(to_index_expr(object).index());
    }
    else if(object.id() == ID_member)
      add_address(to_member_expr(object).compound());
    else if(object.id() == ID_dereference)
      add_read(to_dereference_expr(object).pointer());
    else if(object.id() == ID_typecast)
      add_address(to_typecast_expr(object).op());
    else if(
      object.id() == ID_byte_extract_little_endian ||
      object.id() == ID_byte_extract_big_endian)
    {
      add_address(to_byte_extract_expr(object).op());
      add_read(to_byte_extract_expr(object).offset());
    }
    else if(object.id() == ID_if)
    {
      add_read(to_if_expr(object).cond());
      add_address(to_if_expr(object).true_case());
      add_address(to_if_expr(object).false_case());
    }
    else if(
      object.id() != ID_symbol && !object.is_constant() &&
      object.id() != ID_string_constant && object.id() != ID_label)
    {
      add_read(object);
    }
  }

  void add_write(const exprt &lhs)
  {
    if(lhs.id() == ID_symbol)
    {
      const irep_idt &identifier = to_symbol_expr(lhs).identifier();
      if(!is_excluded(identifier))
        footprint->writes.insert(identifier);
    }
    else if(lhs.id() == ID_index)
    {
      add_write(to_index_expr(lhs).array());
      add_read(to_index_expr(lhs).index());
    }
    else if(lhs.id() == ID_member)
      add_write(to_member_expr(lhs).compound());
    else if(lhs.id() == ID_dereference)
    {
      const exprt &pointer = to_dereference_expr(lhs).pointer();
      add_read(pointer);
      add_pointees(pointer, footprint->writes);
    }
    else if(
      lhs.id() == ID_typecast || lhs.id() == ID_complex_real ||
      lhs.id() == ID_complex_imag)
    {
      add_write(to_unary_expr(lhs).op());
    }
    else if(
      lhs.id() == ID_byte_extract_little_endian ||
      lhs.id() == ID_byte_extract_big_endian)
    {
      add_write(to_byte_extract_expr(lhs).op());
      add_read(to_byte_extract_expr(lhs).offset());
    }
    else if(lhs.id() == ID_if)
    {
      add_read(to_if_expr(lhs).cond());
      add_write(to_if_expr(lhs).true_case());
      add_write(to_if_expr(lhs).false_case());
    }
    else
      footprint->unknown = true;
  }

  /// Add the footprint of \p _target, not including the functions it calls,
  /// which are added to \p callees instead. Direct accesses to parameters
  /// and local variables of \p _excluded_locals are not recorded.
  void add_local(
    const irep_idt &_function,
    goto_programt::const_targett _target,
    const irep_idt &_excluded_locals,
    footprintt &dest,
    std::set<irep_idt> &callees)
  {
    function = _function;
    target = _target;
    excluded_locals = _excluded_locals;
    footprint = &dest;

    switch(target->type())
    {
    case ASSIGN:
      add_write(target->assign_lhs());
      add_read(target->assign_rhs());
      break;
    case DECL:
      add_write(target->decl_symbol());
      break;
    case DEAD:
      add_write(target->dead_symbol());
      break;
    case FUNCTION_CALL:
      if(target->call_lhs().is_not_nil())
        add_write(target->call_lhs());
      for(const auto &argument : target->call_arguments())
        add_read(argument);
      if(target->call_function().id() == ID_symbol)
        callees.insert(to_symbol_expr(target->call_function()).identifier());
      else
        dest.unknown = true;
      break;
    case GOTO:
    case ASSUME:
    case ASSERT:
      add_read(target->condition());
      break;
    case SET_RETURN_VALUE:
      add_read(target->return_value());
      break;
    case OTHER:
    {
      const irep_idt &statement = target->get_other().get_statement();
      if(
        statement == ID_expression || statement == ID_output ||
        statement == ID_printf)
      {
        for(const auto &op : target->get_other().operands())
          add_read(op);
      }
      else
        dest.unknown = true;
      break;
    }
    case SKIP:
    case LOCATION:
    case END_FUNCTION:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
      break;
    case START_THREAD:
    case END_THREAD:
    case THROW:
    case CATCH:
    case INCOMPLETE_GOTO:
    case NO_INSTRUCTION_TYPE:
      dest.unknown = true;
      break;
    }

    footprint = nullptr;
  }

  const function_infot &info(const irep_idt &callee)
  {
    auto entry = function_infos.find(callee);
    if(entry != function_infos.end())
      return entry->second;

    function_infot result;
    const auto f_it = goto_model.goto_functions.function_map.find(callee);
    // Functions without a body have no side effects in symex, other than
    // assigning a nondeterministic return value.
    if(
      f_it != goto_model.goto_functions.function_map.end() &&
      f_it->second.body_available())
    {
      forall_goto_program_instructions(i_it, f_it->second.body)
        add_local(callee, i_it, callee, result.local, result.callees);
    }
    return function_infos.emplace(callee, std::move(result)).first->second;
  }

  /// The footprint of \p root and all functions it may call.
  const footprintt &summary(const irep_idt &root)
  {
    auto entry = summaries.find(root);
    if(entry != summaries.end())
      return entry->second;

    // functions reachable from root
    std::vector<irep_idt> reachable{root};
    std::set<irep_idt> seen{root};
    for(std::size_t i = 0; i < reachable.size(); ++i)
    {
      for(const auto &callee : info(reachable[i]).callees)
      {
        if(seen.insert(callee).second)
          reachable.push_back(callee);
      }
    }

    // fixpoint, as the call graph may be cyclic
    std::unordered_map<irep_idt, footprintt> partial;
    bool changed = true;
    while(changed)
    {
      changed = false;
      for(const auto &f : reachable)
      {
        footprintt &fp = partial[f];
        changed = fp.add(info(f).local) || changed;
        for(const auto &callee : info(f).callees)
        {
          const auto done = summaries.find(callee);
          changed = fp.add(
                      done != summaries.end() ? done->second
                                              : footprintt{partial[callee]}) ||
                    changed;
        }
      }
    }

    for(auto &[f, fp] : partial)
      summaries.emplace(f, std::move(fp));
    return summaries.at(root);
  }
};

/// An event whose pinned copy may be enabled.
struct eventt
{
  irep_idt function;
  goto_programt::targett initialisation;
  irep_idt flag;
  std::vector<irep_idt> unordered;
  /// Empty identifiers denote predecessors that cannot be pinned.
  std::vector<irep_idt> predecessors;
  std::vector<irep_idt> reads;
  footprintt footprint;
  bool commutes = false;
  /// The guards of the copies of the event, and whether they guard the
  /// pinned copy.
  std::vector<std::pair<goto_programt::targett, bool>> copies;
};

std::vector<irep_idt> identifiers(const irept &list)
{
  std::vector<irep_idt> result;
  for(const auto &entry : list.get_sub())
  {
    result.push_back(
      entry.id() == ID_symbol
        ? to_symbol_expr(static_cast<const exprt &>(entry)).identifier()
        : irep_idt{});
  }
  return result;
}

bool mentions(const exprt &expr, const irep_idt &identifier)
{
  return has_subexpr(
    expr,
    [&identifier](const exprt &e)
    {
      return e.id() == ID_symbol &&
             to_symbol_expr(e).identifier() == identifier;
    });
}

/// Returns true if \p instruction mentions \p identifier in any of its
/// expressions.
bool mentions(
  const goto_programt::instructiont &instruction,
  const irep_idt &identifier)
{
  bool found = false;
  instruction.apply([&found, &identifier](const exprt &e)
                    { found = found || mentions(e, identifier); });
  return found;
}
} // namespace

void reduce_evaluation_order(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::map<irep_idt, eventt> events;

  for(auto &[function, goto_function] : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, goto_function.body)
    {
      if(!i_it->is_assign() || i_it->assign_lhs().id() != ID_symbol)
        continue;
      const exprt &rhs = i_it->assign_rhs();
      const irept &unordered = rhs.find(ID_C_evaluation_order_unordered);
      if(rhs != false || unordered.is_nil())
        continue;

      eventt event;
      event.function = function;
      event.initialisation = i_it;
      event.flag = to_symbol_expr(i_it->assign_lhs()).identifier();
      event.unordered = identifiers(unordered);
      event.predecessors =
        identifiers(rhs.find(ID_C_evaluation_order_predecessors));
      event.reads = identifiers(rhs.find(ID_C_evaluation_order_reads));
      events.emplace(event.flag, std::move(event));
    }
  }

  if(events.empty())
    return;

  messaget log{message_handler};
  log.status() << "Evaluation-order reduction" << messaget::eom;

  goto_model.goto_functions.update();
  const namespacet ns(goto_model.symbol_table);
  value_set_analysis_fit value_sets(ns);
  value_sets(goto_model.goto_functions);
  footprint_collectort collector{goto_model, value_sets};

  // the footprints of the copies of each event, and of the reads
  std::map<irep_idt, footprintt> read_footprints;
  std::set<irep_idt> functions;
  for(const auto &[flag, event] : events)
  {
    functions.insert(event.function);
    for(const auto &read : event.reads)
      read_footprints.emplace(read, footprintt{});
  }
  for(const auto &function : functions)
  {
    const goto_programt &body =
      goto_model.goto_functions.function_map.at(function).body;
    forall_goto_program_instructions(i_it, body)
    {
      if(
        i_it->is_assign() && i_it->assign_lhs().id() == ID_symbol &&
        read_footprints.find(to_symbol_expr(i_it->assign_lhs()).identifier()) !=
          read_footprints.end())
      {
        collector.add_instruction(
          function,
          i_it,
          read_footprints[to_symbol_expr(i_it->assign_lhs()).identifier()]);
      }
    }
  }
  for(auto &[flag, event] : events)
  {
    goto_programt &body =
      goto_model.goto_functions.function_map.at(event.function).body;
    Forall_goto_program_instructions(i_it, body)
    {
      if(i_it == event.initialisation || !mentions(*i_it, flag))
        continue;

      if(i_it->is_goto() && !i_it->is_backwards_goto())
      {
        // a copy of the event, guarded by a condition on the flag; the
        // pinned copy is skipped unless the flag is set
        const exprt &condition = i_it->condition();
        event.copies.emplace_back(
          i_it,
          condition.id() == ID_not &&
            to_not_expr(condition).op().id() == ID_symbol &&
            to_symbol_expr(to_not_expr(condition).op()).identifier() == flag);
        for(auto copy_it = std::next(i_it); copy_it != i_it->get_target();
            ++copy_it)
        {
          collector.add_instruction(event.function, copy_it, event.footprint);
        }
      }
      else
      {
        // e.g., an if-converted copy
        collector.add_instruction(event.function, i_it, event.footprint);
      }
    }
  }

  // An event commutes with all unordered events, and cannot change the reads
  // in its window.
  for(auto &[flag, event] : events)
  {
    event.commutes = !event.footprint.unknown;
    for(const auto &other : event.unordered)
    {
      const auto other_it = events.find(other);
      if(
        other_it == events.end() ||
        event.footprint.conflicts_with(other_it->second.footprint))
      {
        event.commutes = false;
      }
    }
    for(const auto &read : event.reads)
    {
      if(event.footprint.may_change(read_footprints[read]))
        event.commutes = false;
    }
  }

  // An event can only be pinned if all its predecessors are.
  bool changed = true;
  while(changed)
  {
    changed = false;
    for(auto &[flag, event] : events)
    {
      if(!event.commutes)
        continue;
      for(const auto &predecessor : event.predecessors)
      {
        const auto predecessor_it = events.find(predecessor);
        if(predecessor_it == events.end() || !predecessor_it->second.commutes)
        {
          event.commutes = false;
          changed = true;
          break;
        }
      }
    }
  }

  // Remove the copies that will not execute, including the checks that
  // goto_check_c has added to them, and replace each flag by its value. For
  // events that cannot be pinned, this yields the same program as without
  // pinned copies.
  for(auto &[flag, event] : events)
  {
    for(auto &[guard_it, is_pinned_copy] : event.copies)
    {
      if(is_pinned_copy == event.commutes)
        continue;
      const auto end = guard_it->get_target();
      for(auto it = guard_it; it != end; ++it)
        it->turn_into_skip();
    }
  }
  std::size_t pinned = 0;
  std::map<irep_idt, replace_symbolt> replacements;
  for(auto &[flag, event] : events)
  {
    const symbol_exprt &flag_expr = to_symbol_expr(
      static_cast<const goto_programt::instructiont &>(*event.initialisation)
        .assign_lhs());
    replacements[event.function].insert(
      flag_expr,
      event.commutes ? static_cast<exprt>(true_exprt{})
                     : static_cast<exprt>(false_exprt{}));
    if(event.commutes)
      ++pinned;
  }
  for(const auto &function_replacements : replacements)
  {
    // not a structured binding, which C++17 does not permit to capture
    const replace_symbolt &replace = function_replacements.second;
    for(auto &instruction :
        goto_model.goto_functions.function_map.at(function_replacements.first)
          .body.instructions)
    {
      if(
        (instruction.is_decl() &&
         events.count(instruction.decl_symbol().identifier()) != 0) ||
        (instruction.is_dead() &&
         events.count(instruction.dead_symbol().identifier()) != 0) ||
        (instruction.is_assign() &&
         instruction.assign_lhs().id() == ID_symbol &&
         events.count(to_symbol_expr(instruction.assign_lhs()).identifier()) !=
           0))
      {
        instruction.turn_into_skip();
        continue;
      }
      instruction.transform(
        [&replace, &ns](exprt expr) -> std::optional<exprt>
        {
          // replace_symbolt returns true if nothing was replaced
          if(replace.replace(expr))
            return {};
          return simplify_expr(std::move(expr), ns);
        });
    }
  }

  log.status() << "Evaluation-order reduction: " << pinned << " of "
               << events.size()
               << " side effects commute with all side effects they are "
                  "unordered with"
               << messaget::eom;
}
