/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Volatile Variables

#include "nondet_volatile.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/fresh_symbol.h>
#include <util/options.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_utils.h>

#include <goto-programs/goto_instruction_code.h>
#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

#include <optional>

#include "wmm/fence.h"

class nondet_volatilet
{
public:
  nondet_volatilet(goto_modelt &goto_model, const optionst &options)
    : goto_model(goto_model), all_nondet(false)
  {
    typecheck_options(options);
  }

  void operator()()
  {
    if(
      !all_nondet && nondet_variables.empty() && variable_models.empty() &&
      write_models.empty())
    {
      return;
    }

    if(has_weak_registers())
      setup_weak_buffers(goto_model.symbol_table);

    for(auto &f : goto_model.goto_functions.function_map)
    {
      nondet_volatile(goto_model.symbol_table, f.first, f.second.body);

      if(has_weak_registers())
      {
        const namespacet ns(goto_model.symbol_table);
        instrument_posted_writes(f.first, f.second.body, ns);
      }
    }

    if(has_weak_registers())
      finalize_weak_buffers(goto_model.symbol_table);

    goto_model.goto_functions.update();
  }

private:
  static bool is_volatile(const namespacet &ns, const typet &src);

  void handle_volatile_expression(
    exprt &expr,
    const namespacet &ns,
    goto_programt &pre,
    goto_programt &post);

  void nondet_volatile_rhs(
    const symbol_table_baset &symbol_table,
    exprt &expr,
    goto_programt &pre,
    goto_programt &post);

  void nondet_volatile_lhs(
    const symbol_table_baset &symbol_table,
    exprt &expr,
    goto_programt &pre,
    goto_programt &post);

  void nondet_volatile(
    symbol_table_baset &symbol_table,
    const irep_idt &function_id,
    goto_programt &goto_program);

  /// Is a write to \p lhs modelled as a device side effect (so that it should
  /// be preserved as an observable event)? True for any volatile lvalue in
  /// --nondet-volatile mode, and for the specifically-selected variables in
  /// the scoped (--nondet-volatile-variable / --nondet-volatile-model) modes.
  bool is_modeled_volatile_write(const exprt &lhs, const namespacet &ns) const;

  /// Instrument a write to a volatile lvalue as an observable device side
  /// effect: route it to the configured write model, or otherwise emit an
  /// OUTPUT of the written value so the store is not sliced away as dead.
  void observe_volatile_write(
    const goto_programt::instructiont &instruction,
    const irep_idt &function_id,
    const namespacet &ns,
    goto_programt &post);

  /// Is \p instruction a full memory barrier (a fence, or a call to
  /// __sync_synchronize)? Used as a flush point for the weak MMIO model.
  static bool is_barrier(
    const goto_programt::instructiont &instruction,
    const namespacet &ns);

  /// Is \p instruction a completion barrier (ARM DSB): a full fence not marked
  /// ordering-only, or __sync_synchronize? Under early-ack it completes writes.
  static bool is_completion_barrier(
    const goto_programt::instructiont &instruction,
    const namespacet &ns);

  /// Is \p instruction an ordering-only barrier (ARM DMB / Power lwsync)? Under
  /// early-ack it orders posted writes (by generation) but does not complete
  /// them.
  static bool is_ordering_barrier(
    const goto_programt::instructiont &instruction,
    const namespacet &ns);

  /// A per-register FIFO of posted (not-yet-observed) writes to a weakly
  /// ordered register: a fixed-capacity buffer and its current size. The
  /// buffers have static lifetime so that a posted write can be delayed across
  /// function boundaries, until a barrier or the end of the program.
  struct posted_buffert
  {
    symbol_exprt buffer; // array [weak_depth] of the register's value type
    symbol_exprt size;   // number of pending writes, 0..weak_depth
    irep_idt model;
    // parallel array of the generation each pending write was issued in; only
    // populated under the early-acknowledgement model (--mmio-early-ack)
    std::optional<symbol_exprt> generations;
  };

  /// Create the static posted-write buffers (one per weakly-ordered
  /// write-modelled register) and the shared non-deterministic flush choice.
  void setup_weak_buffers(symbol_table_baset &symbol_table);

  /// Initialise the buffer sizes at the start of the entry point and flush any
  /// writes still posted at the end of the program.
  void finalize_weak_buffers(symbol_table_baset &symbol_table);

  // helpers building goto fragments for the weak MMIO model; see the
  // definitions for the exact semantics
  void emit_observe_head(
    goto_programt &dest,
    const posted_buffert &b,
    const namespacet &ns,
    const source_locationt &loc) const;
  void emit_flush_one(
    goto_programt &dest,
    const posted_buffert &b,
    const namespacet &ns,
    const source_locationt &loc) const;
  void emit_nondet_flush(
    goto_programt &dest,
    const posted_buffert &b,
    const namespacet &ns,
    const source_locationt &loc) const;
  void emit_enqueue(
    goto_programt &dest,
    const posted_buffert &b,
    const exprt &value,
    const namespacet &ns,
    const source_locationt &loc) const;

  /// The condition (used under --mmio-early-ack) under which the head of \p b
  /// is in the globally-oldest barrier generation, so it may be observed now;
  /// true_exprt when early-ack is off.
  exprt head_is_oldest(const posted_buffert &b) const;

  /// Flush all posted writes (a completion barrier / DSB, or program end),
  /// observing them in generation order under early-ack.
  void emit_drain_all(
    goto_programt &dest,
    const namespacet &ns,
    const source_locationt &loc) const;

  /// Weak MMIO model (--mmio-weak): make writes to weakly-ordered
  /// write-modelled registers "posted". Each such write is enqueued and its
  /// write-model call is delivered non-deterministically at this or a later
  /// point, or at a barrier, or at the end of the program. A write to one
  /// register may thus be observed after a later write to another register,
  /// exposing missing-barrier ordering bugs, while a barrier forces in-order
  /// observation.
  void instrument_posted_writes(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const namespacet &ns);

  const symbolt &typecheck_variable(const irep_idt &id, const namespacet &ns);

  void typecheck_model(
    const irep_idt &id,
    const symbolt &variable,
    const namespacet &ns);

  void typecheck_write_model(
    const irep_idt &id,
    const symbolt &variable,
    const namespacet &ns);

  void typecheck_options(const optionst &options);

  goto_modelt &goto_model;

  // configuration obtained from command line options
  bool all_nondet;
  std::set<irep_idt> nondet_variables;
  std::map<irep_idt, irep_idt> variable_models;
  std::map<irep_idt, irep_idt> write_models;

  // weak MMIO model: which registers are weakly ordered (--mmio-weak marks all
  // write-modelled registers; --mmio-weak-variable marks specific ones)
  bool all_weak = false;
  std::set<irep_idt> weak_registers;

  // depth of the per-register posted-write FIFO (--mmio-weak-depth); a larger
  // depth allows more outstanding writes and hence deeper reordering
  std::size_t weak_depth = 1;

  // write combining (--mmio-gather): a write to a weakly-ordered register may
  // be merged into the most recent not-yet-observed write to the same register
  bool gather = false;

  // early acknowledgement (--mmio-early-ack): a lightweight fence acts as an
  // ordering barrier (ARM DMB) -- it orders posted writes by generation but
  // does not complete them -- while a full fence is a completion barrier (DSB)
  bool early_ack = false;

  // the current barrier generation (--mmio-early-ack), bumped at each ordering
  // barrier; posted writes are tagged with, and observed in, generation order
  std::optional<symbol_exprt> current_gen;

  // the static posted-write buffers, one per weakly-ordered register, and the
  // shared non-deterministic flush choice (populated by setup_weak_buffers)
  std::map<irep_idt, posted_buffert> weak_buffers;
  std::optional<symbol_exprt> flush_choice;

  /// Is the register \p id modelled as weakly ordered device memory?
  bool is_weak_register(const irep_idt &id) const
  {
    return all_weak || weak_registers.count(id) != 0;
  }

  /// Is any register modelled as weakly ordered?
  bool has_weak_registers() const
  {
    return all_weak || !weak_registers.empty();
  }
};

bool nondet_volatilet::is_volatile(const namespacet &ns, const typet &src)
{
  if(src.get_bool(ID_C_volatile))
    return true;

  if(auto struct_tag = type_try_dynamic_cast<struct_tag_typet>(src))
    return is_volatile(ns, ns.follow_tag(*struct_tag));
  else if(auto union_tag = type_try_dynamic_cast<union_tag_typet>(src))
    return is_volatile(ns, ns.follow_tag(*union_tag));
  else if(auto enum_tag = type_try_dynamic_cast<c_enum_tag_typet>(src))
    return is_volatile(ns, ns.follow_tag(*enum_tag));
  else
    return false;
}

void nondet_volatilet::handle_volatile_expression(
  exprt &expr,
  const namespacet &ns,
  goto_programt &pre,
  goto_programt &post)
{
  // Check if we should replace the variable by a nondet expression
  if(
    all_nondet ||
    (expr.id() == ID_symbol &&
     nondet_variables.count(to_symbol_expr(expr).identifier()) != 0))
  {
    typet t = expr.type();
    t.remove(ID_C_volatile);

    side_effect_expr_nondett nondet_expr(t, expr.source_location());
    expr.swap(nondet_expr);

    return;
  }

  // Now check if we should replace the variable by a model

  if(expr.id() != ID_symbol)
  {
    return;
  }

  const irep_idt &id = to_symbol_expr(expr).identifier();
  const auto &it = variable_models.find(id);

  if(it == variable_models.end())
  {
    return;
  }

  const auto &model_symbol = ns.lookup(it->second);

  const auto &new_variable = get_fresh_aux_symbol(
                               to_code_type(model_symbol.type).return_type(),
                               "",
                               "modelled_volatile",
                               source_locationt(),
                               ID_C,
                               goto_model.symbol_table)
                               .symbol_expr();

  pre.instructions.push_back(goto_programt::make_decl(new_variable));

  code_function_callt call(new_variable, model_symbol.symbol_expr(), {});
  pre.instructions.push_back(goto_programt::make_function_call(call));

  post.instructions.push_back(goto_programt::make_dead(new_variable));

  expr = new_variable;
}

void nondet_volatilet::nondet_volatile_rhs(
  const symbol_table_baset &symbol_table,
  exprt &expr,
  goto_programt &pre,
  goto_programt &post)
{
  Forall_operands(it, expr)
    nondet_volatile_rhs(symbol_table, *it, pre, post);

  if(expr.id() == ID_symbol || expr.id() == ID_dereference)
  {
    const namespacet ns(symbol_table);

    if(is_volatile(ns, expr.type()))
    {
      handle_volatile_expression(expr, ns, pre, post);
    }
  }
}

void nondet_volatilet::nondet_volatile_lhs(
  const symbol_table_baset &symbol_table,
  exprt &expr,
  goto_programt &pre,
  goto_programt &post)
{
  if(expr.id() == ID_if)
  {
    nondet_volatile_rhs(symbol_table, to_if_expr(expr).cond(), pre, post);
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).true_case(), pre, post);
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).false_case(), pre, post);
  }
  else if(expr.id() == ID_index)
  {
    nondet_volatile_lhs(symbol_table, to_index_expr(expr).array(), pre, post);
    nondet_volatile_rhs(symbol_table, to_index_expr(expr).index(), pre, post);
  }
  else if(expr.id() == ID_member)
  {
    nondet_volatile_lhs(
      symbol_table, to_member_expr(expr).struct_op(), pre, post);
  }
  else if(expr.id() == ID_dereference)
  {
    nondet_volatile_rhs(
      symbol_table, to_dereference_expr(expr).pointer(), pre, post);
  }
}

bool nondet_volatilet::is_modeled_volatile_write(
  const exprt &lhs,
  const namespacet &ns) const
{
  if(all_nondet)
    return is_volatile(ns, lhs.type());

  if(lhs.id() == ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(lhs).identifier();
    return nondet_variables.count(id) != 0 || variable_models.count(id) != 0;
  }

  return false;
}

void nondet_volatilet::observe_volatile_write(
  const goto_programt::instructiont &instruction,
  const irep_idt &function_id,
  const namespacet &ns,
  goto_programt &post)
{
  // The zero-initialisation of globals in the CPROVER initialisation function
  // is a language-level artefact, not an action on the device, so it is not
  // treated as an observable device write.
  if(function_id == INITIALIZE_FUNCTION)
    return;

  const exprt &lhs = instruction.assign_lhs();

  // A write model configured for this register observes (and can assert on)
  // the written value; it supersedes the default observable output.
  if(lhs.id() == ID_symbol)
  {
    const auto it = write_models.find(to_symbol_expr(lhs).identifier());

    if(it != write_models.end())
    {
      // A write to a weakly-ordered register is observed by the posted-write
      // instrumentation (possibly reordered); for a strongly-ordered register
      // the model is called here, in program order. Either way there is no
      // default observable OUTPUT for a write-modelled register.
      if(!is_weak_register(it->first))
      {
        const symbolt &model_symbol = ns.lookup(it->second);

        post.instructions.push_back(goto_programt::make_function_call(
          code_function_callt{
            model_symbol.symbol_expr(), {instruction.assign_rhs()}},
          instruction.source_location()));
      }

      return;
    }
  }

  // Otherwise, if this register is modelled as a device, a write to it is an
  // observable side effect: it acts on the device rather than merely updating
  // storage the program later reads. When volatile reads are modelled
  // non-deterministically the written value is never read back, so without
  // this the store would be sliced away as dead. Emit an OUTPUT of the written
  // value so the write is preserved and appears in counterexample traces.
  if(is_modeled_volatile_write(lhs, ns))
  {
    post.instructions.push_back(goto_programt::make_other(
      code_outputt{
        "volatile-write",
        instruction.assign_rhs(),
        instruction.source_location()},
      instruction.source_location()));
  }
}

bool nondet_volatilet::is_barrier(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  // a full fence, e.g. __CPROVER_fence with all of WW/WR/RW/RR set
  if(is_fence(instruction, ns))
    return true;

  // a call to __sync_synchronize (the gcc/Linux full memory barrier)
  if(instruction.is_function_call())
  {
    const exprt &function = instruction.call_function();
    if(function.id() == ID_symbol)
    {
      return ns.lookup(to_symbol_expr(function)).base_name ==
             "__sync_synchronize";
    }
  }

  return false;
}

bool nondet_volatilet::is_completion_barrier(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  // __sync_synchronize is a full/completion barrier
  if(instruction.is_function_call())
  {
    const exprt &function = instruction.call_function();
    if(
      function.id() == ID_symbol &&
      ns.lookup(to_symbol_expr(function)).base_name == "__sync_synchronize")
    {
      return true;
    }
  }

  // a full fence that is not marked ordering-only (ARM DSB, or an explicit full
  // fence)
  return is_fence(instruction, ns) &&
         !instruction.code().get_bool(ID_ordering_fence);
}

bool nondet_volatilet::is_ordering_barrier(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  // ARM DMB: a full fence marked ordering-only
  if(is_fence(instruction, ns))
    return instruction.code().get_bool(ID_ordering_fence);

  // Power lwsync / a lightweight fence
  return is_lwfence(instruction, ns);
}

exprt nondet_volatilet::head_is_oldest(const posted_buffert &b) const
{
  if(!early_ack)
    return true_exprt{};

  PRECONDITION(b.generations.has_value());
  const typet index_type = size_type();
  const exprt zero = from_integer(0, index_type);
  const exprt b_head_gen = index_exprt{*b.generations, zero};

  exprt result = true_exprt{};
  for(const auto &other : weak_buffers)
  {
    if(other.second.buffer == b.buffer)
      continue;
    PRECONDITION(other.second.generations.has_value());
    // the other register is empty, or its head is not older than b's head
    const or_exprt condition{
      equal_exprt{other.second.size, zero},
      binary_relation_exprt{
        index_exprt{*other.second.generations, zero}, ID_ge, b_head_gen}};
    if(result.is_true())
      result = condition;
    else
      result = and_exprt{result, condition};
  }

  return result;
}

// observe (call the model for) the head of the FIFO and shift the remaining
// entries down; the caller guarantees the buffer is non-empty
void nondet_volatilet::emit_observe_head(
  goto_programt &dest,
  const posted_buffert &b,
  const namespacet &ns,
  const source_locationt &loc) const
{
  const typet index_type = size_type();
  const exprt zero = from_integer(0, index_type);
  const exprt one = from_integer(1, index_type);

  dest.add(goto_programt::make_function_call(
    code_function_callt{
      ns.lookup(b.model).symbol_expr(), {index_exprt{b.buffer, zero}}},
    loc));
  for(std::size_t i = 0; i + 1 < weak_depth; ++i)
  {
    dest.add(goto_programt::make_assignment(
      index_exprt{b.buffer, from_integer(i, index_type)},
      index_exprt{b.buffer, from_integer(i + 1, index_type)},
      loc));
    if(early_ack)
    {
      dest.add(goto_programt::make_assignment(
        index_exprt{*b.generations, from_integer(i, index_type)},
        index_exprt{*b.generations, from_integer(i + 1, index_type)},
        loc));
    }
  }
  dest.add(
    goto_programt::make_assignment(b.size, minus_exprt{b.size, one}, loc));
}

// if(size != 0 && head is oldest) observe_head -- an unconditional flush of the
// oldest observable entry (the generation guard is trivial without early-ack)
void nondet_volatilet::emit_flush_one(
  goto_programt &dest,
  const posted_buffert &b,
  const namespacet &ns,
  const source_locationt &loc) const
{
  const exprt zero = from_integer(0, size_type());
  exprt skip_condition = equal_exprt{b.size, zero};
  if(early_ack)
    skip_condition = or_exprt{skip_condition, not_exprt{head_is_oldest(b)}};
  auto guard =
    dest.add(goto_programt::make_incomplete_goto(skip_condition, loc));
  emit_observe_head(dest, b, ns, loc);
  auto label = dest.add(goto_programt::make_skip(loc));
  guard->complete_goto(label);
}

// if(size != 0 && nondet) observe_head -- a non-deterministic flush that lets
// a posted write be observed (or not) here, which is what produces reordering
void nondet_volatilet::emit_nondet_flush(
  goto_programt &dest,
  const posted_buffert &b,
  const namespacet &ns,
  const source_locationt &loc) const
{
  PRECONDITION(flush_choice.has_value());
  const exprt zero = from_integer(0, size_type());
  dest.add(goto_programt::make_assignment(
    *flush_choice, side_effect_expr_nondett{bool_typet{}, loc}, loc));
  exprt skip_condition =
    or_exprt{equal_exprt{b.size, zero}, not_exprt{*flush_choice}};
  if(early_ack)
    skip_condition = or_exprt{skip_condition, not_exprt{head_is_oldest(b)}};
  auto guard =
    dest.add(goto_programt::make_incomplete_goto(skip_condition, loc));
  emit_observe_head(dest, b, ns, loc);
  auto label = dest.add(goto_programt::make_skip(loc));
  guard->complete_goto(label);
}

// enqueue value at the tail; if the buffer is full, observe the head first to
// make room (a bounded over-approximation of an unbounded buffer)
void nondet_volatilet::emit_enqueue(
  goto_programt &dest,
  const posted_buffert &b,
  const exprt &value,
  const namespacet &ns,
  const source_locationt &loc) const
{
  const typet index_type = size_type();
  const exprt zero = from_integer(0, index_type);
  const exprt one = from_integer(1, index_type);
  const exprt capacity = from_integer(weak_depth, index_type);

  // append value at the tail, observing the head first if the buffer is full
  const auto emit_append = [&](goto_programt &d)
  {
    auto guard = d.add(goto_programt::make_incomplete_goto(
      notequal_exprt{b.size, capacity}, loc));
    emit_observe_head(d, b, ns, loc);
    auto label = d.add(goto_programt::make_skip(loc));
    guard->complete_goto(label);
    d.add(goto_programt::make_assignment(
      index_exprt{b.buffer, b.size}, value, loc));
    if(early_ack)
    {
      d.add(goto_programt::make_assignment(
        index_exprt{*b.generations, b.size}, *current_gen, loc));
    }
    d.add(goto_programt::make_assignment(b.size, plus_exprt{b.size, one}, loc));
  };

  if(!gather)
  {
    emit_append(dest);
    return;
  }

  // write combining: if there is a not-yet-observed write to this register, the
  // new write may (non-deterministically) be merged into it -- the device then
  // observes only the merged (latest) value -- instead of being appended
  PRECONDITION(flush_choice.has_value());
  dest.add(goto_programt::make_assignment(
    *flush_choice, side_effect_expr_nondett{bool_typet{}, loc}, loc));
  auto to_append = dest.add(goto_programt::make_incomplete_goto(
    or_exprt{equal_exprt{b.size, zero}, not_exprt{*flush_choice}}, loc));
  dest.add(goto_programt::make_assignment(
    index_exprt{b.buffer, minus_exprt{b.size, one}}, value, loc));
  auto to_done =
    dest.add(goto_programt::make_incomplete_goto(true_exprt{}, loc));
  auto append_label = dest.add(goto_programt::make_skip(loc));
  to_append->complete_goto(append_label);
  emit_append(dest);
  auto done_label = dest.add(goto_programt::make_skip(loc));
  to_done->complete_goto(done_label);
}

void nondet_volatilet::emit_drain_all(
  goto_programt &dest,
  const namespacet &ns,
  const source_locationt &loc) const
{
  // Enough passes to drain every entry: under early-ack each pass observes the
  // current oldest generation, so at most (registers * depth) passes are
  // needed; without early-ack a single flush per slot already drains.
  const std::size_t passes = weak_buffers.size() * weak_depth;
  for(std::size_t p = 0; p < passes; ++p)
    for(const auto &b : weak_buffers)
      emit_flush_one(dest, b.second, ns, loc);
}

void nondet_volatilet::setup_weak_buffers(symbol_table_baset &symbol_table)
{
  const namespacet ns(symbol_table);
  const typet index_type = size_type();
  const exprt capacity = from_integer(weak_depth, index_type);

  // one static FIFO per weakly-ordered write-modelled register; static lifetime
  // lets a posted write be delayed across function boundaries
  for(const auto &write_model : write_models)
  {
    if(!is_weak_register(write_model.first))
      continue;

    const symbolt &register_symbol = ns.lookup(write_model.first);
    const array_typet buffer_type{register_symbol.type, capacity};

    symbolt &buffer_symbol = get_fresh_aux_symbol(
      buffer_type, "", "mmio_posted", source_locationt{}, ID_C, symbol_table);
    buffer_symbol.is_static_lifetime = true;
    buffer_symbol.is_thread_local = false;

    symbolt &size_symbol = get_fresh_aux_symbol(
      index_type,
      "",
      "mmio_posted_size",
      source_locationt{},
      ID_C,
      symbol_table);
    size_symbol.is_static_lifetime = true;
    size_symbol.is_thread_local = false;

    posted_buffert entry{
      buffer_symbol.symbol_expr(),
      size_symbol.symbol_expr(),
      write_model.second};

    if(early_ack)
    {
      const array_typet generation_type{index_type, capacity};
      symbolt &generation_symbol = get_fresh_aux_symbol(
        generation_type,
        "",
        "mmio_posted_gen",
        source_locationt{},
        ID_C,
        symbol_table);
      generation_symbol.is_static_lifetime = true;
      generation_symbol.is_thread_local = false;
      entry.generations = generation_symbol.symbol_expr();
    }

    weak_buffers.emplace(write_model.first, entry);
  }

  if(weak_buffers.empty())
    return;

  if(early_ack)
  {
    symbolt &generation_symbol = get_fresh_aux_symbol(
      index_type, "", "mmio_gen", source_locationt{}, ID_C, symbol_table);
    generation_symbol.is_static_lifetime = true;
    generation_symbol.is_thread_local = false;
    current_gen = generation_symbol.symbol_expr();
  }

  symbolt &choice_symbol = get_fresh_aux_symbol(
    bool_typet{},
    "",
    "mmio_flush_choice",
    source_locationt{},
    ID_C,
    symbol_table);
  choice_symbol.is_static_lifetime = true;
  choice_symbol.is_thread_local = false;
  flush_choice = choice_symbol.symbol_expr();
}

void nondet_volatilet::finalize_weak_buffers(symbol_table_baset &symbol_table)
{
  if(weak_buffers.empty())
    return;

  const namespacet ns(symbol_table);
  const exprt zero = from_integer(0, size_type());
  const source_locationt loc{};

  auto entry =
    goto_model.goto_functions.function_map.find(goto_functionst::entry_point());
  if(
    entry == goto_model.goto_functions.function_map.end() ||
    !entry->second.body_available())
  {
    return;
  }

  goto_programt &body = entry->second.body;

  // initialise the buffer sizes (and the generation counter) at the very start
  // of the program
  goto_programt initialisations;
  for(const auto &b : weak_buffers)
    initialisations.add(
      goto_programt::make_assignment(b.second.size, zero, loc));
  if(early_ack)
    initialisations.add(
      goto_programt::make_assignment(*current_gen, zero, loc));
  body.destructive_insert(body.instructions.begin(), initialisations);

  // flush any writes still posted when the program ends
  auto end = std::prev(body.instructions.end());
  goto_programt epilogue;
  emit_drain_all(epilogue, ns, loc);
  body.destructive_insert(end, epilogue);
}

void nondet_volatilet::instrument_posted_writes(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const namespacet &ns)
{
  if(weak_buffers.empty())
    return;

  // the zero-initialisation of the volatile globals is not a device action
  if(function_id == INITIALIZE_FUNCTION)
    return;

  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it)
  {
    if(it->is_assign() && it->assign_lhs().id() == ID_symbol)
    {
      const auto b_it =
        weak_buffers.find(to_symbol_expr(it->assign_lhs()).identifier());

      if(b_it != weak_buffers.end())
      {
        const source_locationt loc = it->source_location();
        goto_programt fragment;
        // post the write, then give every register's buffer a chance to be
        // (partly) observed here, which is what produces the reordering
        emit_enqueue(fragment, b_it->second, it->assign_rhs(), ns, loc);
        for(const auto &b : weak_buffers)
          for(std::size_t k = 0; k < weak_depth; ++k)
            emit_nondet_flush(fragment, b.second, ns, loc);
        goto_program.destructive_insert(std::next(it), fragment);
      }
    }
    else if(!early_ack && is_barrier(*it, ns))
    {
      // without early-ack, any barrier completes all posted writes
      const source_locationt loc = it->source_location();
      goto_programt fragment;
      emit_drain_all(fragment, ns, loc);
      goto_program.destructive_insert(std::next(it), fragment);
    }
    else if(early_ack && is_completion_barrier(*it, ns))
    {
      // a completion barrier (a full fence / __sync_synchronize, i.e. an ARM
      // DSB) completes all posted writes
      const source_locationt loc = it->source_location();
      goto_programt fragment;
      emit_drain_all(fragment, ns, loc);
      goto_program.destructive_insert(std::next(it), fragment);
    }
    else if(early_ack && is_ordering_barrier(*it, ns))
    {
      // an ordering barrier (ARM DMB / Power lwsync) orders posted writes by
      // generation but does not complete them: bump the generation, so later
      // writes cannot be observed before writes posted before it
      const source_locationt loc = it->source_location();
      goto_programt fragment;
      fragment.add(goto_programt::make_assignment(
        *current_gen,
        plus_exprt{*current_gen, from_integer(1, size_type())},
        loc));
      goto_program.destructive_insert(std::next(it), fragment);
    }
  }
}

void nondet_volatilet::nondet_volatile(
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  goto_programt &goto_program)
{
  namespacet ns(symbol_table);

  for(auto i_it = goto_program.instructions.begin();
      i_it != goto_program.instructions.end();
      i_it++)
  {
    goto_programt pre;
    goto_programt post;

    goto_programt::instructiont &instruction = *i_it;

    if(instruction.is_assign())
    {
      nondet_volatile_rhs(
        symbol_table, instruction.assign_rhs_nonconst(), pre, post);
      nondet_volatile_lhs(
        symbol_table, instruction.assign_lhs_nonconst(), pre, post);

      observe_volatile_write(instruction, function_id, ns, post);
    }
    else if(instruction.is_function_call())
    {
      // these have arguments and a return LHS

      code_function_callt &code_function_call =
        to_code_function_call(instruction.code_nonconst());

      // do arguments
      for(exprt::operandst::iterator it =
            code_function_call.arguments().begin();
          it != code_function_call.arguments().end();
          it++)
        nondet_volatile_rhs(symbol_table, *it, pre, post);

      // do return value
      nondet_volatile_lhs(symbol_table, code_function_call.lhs(), pre, post);
    }
    else if(instruction.has_condition())
    {
      // do condition
      nondet_volatile_rhs(
        symbol_table, instruction.condition_nonconst(), pre, post);
    }

    const auto pre_size = pre.instructions.size();
    goto_program.insert_before_swap(i_it, pre);
    std::advance(i_it, pre_size);

    const auto post_size = post.instructions.size();
    goto_program.destructive_insert(std::next(i_it), post);
    std::advance(i_it, post_size);
  }
}

const symbolt &
nondet_volatilet::typecheck_variable(const irep_idt &id, const namespacet &ns)
{
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
  {
    throw invalid_command_line_argument_exceptiont(
      "given symbol `" + id2string(id) + "` not found in symbol table",
      "--" NONDET_VOLATILE_VARIABLE_OPT);
  }

  if(!symbol->is_static_lifetime || !symbol->type.get_bool(ID_C_volatile))
  {
    throw invalid_command_line_argument_exceptiont(
      "symbol `" + id2string(id) +
        "` does not represent a volatile variable "
        "with static lifetime",
      "--" NONDET_VOLATILE_VARIABLE_OPT);
  }

  INVARIANT(!symbol->is_type, "symbol must not represent a type");

  INVARIANT(!symbol->is_function(), "symbol must not represent a function");

  return *symbol;
}

void nondet_volatilet::typecheck_model(
  const irep_idt &id,
  const symbolt &variable,
  const namespacet &ns)
{
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
  {
    throw invalid_command_line_argument_exceptiont(
      "given model name " + id2string(id) + " not found in symbol table",
      "--" NONDET_VOLATILE_MODEL_OPT);
  }

  if(!symbol->is_function())
  {
    throw invalid_command_line_argument_exceptiont(
      "symbol `" + id2string(id) + "` is not a function",
      "--" NONDET_VOLATILE_MODEL_OPT);
  }

  const auto &code_type = to_code_type(symbol->type);

  if(variable.type != code_type.return_type())
  {
    throw invalid_command_line_argument_exceptiont(
      "return type of model `" + id2string(id) +
        "` is not compatible with the "
        "type of the modelled variable " +
        id2string(variable.name),
      "--" NONDET_VOLATILE_MODEL_OPT);
  }

  if(!code_type.parameters().empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "model `" + id2string(id) + "` must not take parameters ",
      "--" NONDET_VOLATILE_MODEL_OPT);
  }
}

void nondet_volatilet::typecheck_write_model(
  const irep_idt &id,
  const symbolt &variable,
  const namespacet &ns)
{
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
  {
    throw invalid_command_line_argument_exceptiont(
      "given write model name " + id2string(id) + " not found in symbol table",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  if(!symbol->is_function())
  {
    throw invalid_command_line_argument_exceptiont(
      "symbol `" + id2string(id) + "` is not a function",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  const auto &code_type = to_code_type(symbol->type);

  if(code_type.return_type().id() != ID_empty)
  {
    throw invalid_command_line_argument_exceptiont(
      "write model `" + id2string(id) + "` must return void",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  if(code_type.parameters().size() != 1)
  {
    throw invalid_command_line_argument_exceptiont(
      "write model `" + id2string(id) +
        "` must take exactly one parameter (the written value)",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  if(variable.type != code_type.parameters().front().type())
  {
    throw invalid_command_line_argument_exceptiont(
      "parameter type of write model `" + id2string(id) +
        "` is not compatible with the type of the modelled variable " +
        id2string(variable.name),
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }
}

void nondet_volatilet::typecheck_options(const optionst &options)
{
  PRECONDITION(!all_nondet);
  PRECONDITION(nondet_variables.empty());
  PRECONDITION(variable_models.empty());
  PRECONDITION(write_models.empty());

  const namespacet ns(goto_model.symbol_table);

  // the weak MMIO model is independent of the read-side mode
  if(options.get_bool_option(MMIO_WEAK_OPT))
    all_weak = true;

  if(options.is_set(MMIO_WEAK_VARIABLE_OPT))
  {
    const auto &variable_list = options.get_list_option(MMIO_WEAK_VARIABLE_OPT);

    for(const auto &id : variable_list)
    {
      typecheck_variable(id, ns);
      weak_registers.insert(id);
    }
  }

  if(options.is_set(MMIO_WEAK_DEPTH_OPT))
  {
    const auto depth = options.get_unsigned_int_option(MMIO_WEAK_DEPTH_OPT);

    if(depth < 1)
    {
      throw invalid_command_line_argument_exceptiont(
        "the weak MMIO buffer depth must be at least 1",
        "--" MMIO_WEAK_DEPTH_OPT);
    }

    weak_depth = depth;
  }

  if(options.get_bool_option(MMIO_GATHER_OPT))
    gather = true;

  if(options.get_bool_option(MMIO_EARLY_ACK_OPT))
    early_ack = true;

  // Write models are independent of the read-side mode and may be combined
  // with any of them (including --nondet-volatile), so they are processed
  // before the read-side options.
  if(options.is_set(NONDET_VOLATILE_WRITE_MODEL_OPT))
  {
    const auto &model_list =
      options.get_list_option(NONDET_VOLATILE_WRITE_MODEL_OPT);

    for(const auto &s : model_list)
    {
      std::string variable;
      std::string model;

      try
      {
        split_string(s, ':', variable, model, true);
      }
      catch(const deserialization_exceptiont &)
      {
        throw invalid_command_line_argument_exceptiont(
          "cannot split argument `" + s + "` into variable name and model name",
          "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
      }

      const auto &variable_symbol = typecheck_variable(variable, ns);

      typecheck_write_model(model, variable_symbol, ns);

      const auto p = write_models.insert(std::make_pair(variable, model));

      if(!p.second && p.first->second != model)
      {
        throw invalid_command_line_argument_exceptiont(
          "conflicting write models for variable `" + variable + "`",
          "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
      }
    }
  }

  if(options.get_bool_option(NONDET_VOLATILE_OPT))
  {
    all_nondet = true;
    return;
  }

  if(options.is_set(NONDET_VOLATILE_VARIABLE_OPT))
  {
    const auto &variable_list =
      options.get_list_option(NONDET_VOLATILE_VARIABLE_OPT);

    nondet_variables.insert(variable_list.begin(), variable_list.end());

    for(const auto &id : nondet_variables)
    {
      typecheck_variable(id, ns);
    }
  }

  if(options.is_set(NONDET_VOLATILE_MODEL_OPT))
  {
    const auto &model_list = options.get_list_option(NONDET_VOLATILE_MODEL_OPT);

    for(const auto &s : model_list)
    {
      std::string variable;
      std::string model;

      try
      {
        split_string(s, ':', variable, model, true);
      }
      catch(const deserialization_exceptiont &e)
      {
        throw invalid_command_line_argument_exceptiont(
          "cannot split argument `" + s + "` into variable name and model name",
          "--" NONDET_VOLATILE_MODEL_OPT);
      }

      const auto &variable_symbol = typecheck_variable(variable, ns);

      if(nondet_variables.count(variable) != 0)
      {
        throw invalid_command_line_argument_exceptiont(
          "conflicting options for variable `" + variable + "`",
          "--" NONDET_VOLATILE_VARIABLE_OPT "/--" NONDET_VOLATILE_MODEL_OPT);
      }

      typecheck_model(model, variable_symbol, ns);

      const auto p = variable_models.insert(std::make_pair(variable, model));

      if(!p.second && p.first->second != model)
      {
        throw invalid_command_line_argument_exceptiont(
          "conflicting models for variable `" + variable + "`",
          "--" NONDET_VOLATILE_MODEL_OPT);
      }
    }
  }
}

void parse_nondet_volatile_options(const cmdlinet &cmdline, optionst &options)
{
  PRECONDITION(!options.is_set(NONDET_VOLATILE_OPT));
  PRECONDITION(!options.is_set(NONDET_VOLATILE_VARIABLE_OPT));
  PRECONDITION(!options.is_set(NONDET_VOLATILE_MODEL_OPT));
  PRECONDITION(!options.is_set(NONDET_VOLATILE_WRITE_MODEL_OPT));
  PRECONDITION(!options.is_set(MMIO_WEAK_OPT));
  PRECONDITION(!options.is_set(MMIO_WEAK_VARIABLE_OPT));
  PRECONDITION(!options.is_set(MMIO_WEAK_DEPTH_OPT));
  PRECONDITION(!options.is_set(MMIO_GATHER_OPT));
  PRECONDITION(!options.is_set(MMIO_EARLY_ACK_OPT));

  const bool nondet_volatile_opt = cmdline.isset(NONDET_VOLATILE_OPT);
  const bool nondet_volatile_variable_opt =
    cmdline.isset(NONDET_VOLATILE_VARIABLE_OPT);
  const bool nondet_volatile_model_opt =
    cmdline.isset(NONDET_VOLATILE_MODEL_OPT);

  if(
    nondet_volatile_opt &&
    (nondet_volatile_variable_opt || nondet_volatile_model_opt))
  {
    throw invalid_command_line_argument_exceptiont(
      "--" NONDET_VOLATILE_OPT
      " cannot be used with --" NONDET_VOLATILE_VARIABLE_OPT
      " or --" NONDET_VOLATILE_MODEL_OPT,
      "--" NONDET_VOLATILE_OPT "/--" NONDET_VOLATILE_VARIABLE_OPT
      "/--" NONDET_VOLATILE_MODEL_OPT);
  }

  if(nondet_volatile_opt)
  {
    options.set_option(NONDET_VOLATILE_OPT, true);
  }
  else
  {
    if(nondet_volatile_variable_opt)
    {
      options.set_option(
        NONDET_VOLATILE_VARIABLE_OPT,
        cmdline.get_values(NONDET_VOLATILE_VARIABLE_OPT));
    }

    if(nondet_volatile_model_opt)
    {
      options.set_option(
        NONDET_VOLATILE_MODEL_OPT,
        cmdline.get_values(NONDET_VOLATILE_MODEL_OPT));
    }
  }

  // Write models are independent of the (mutually-exclusive) read-side modes
  // and may be combined with any of them.
  if(cmdline.isset(NONDET_VOLATILE_WRITE_MODEL_OPT))
  {
    options.set_option(
      NONDET_VOLATILE_WRITE_MODEL_OPT,
      cmdline.get_values(NONDET_VOLATILE_WRITE_MODEL_OPT));
  }

  // The weak MMIO model is likewise independent of the read-side mode.
  if(cmdline.isset(MMIO_WEAK_OPT))
  {
    options.set_option(MMIO_WEAK_OPT, true);
  }

  if(cmdline.isset(MMIO_WEAK_VARIABLE_OPT))
  {
    options.set_option(
      MMIO_WEAK_VARIABLE_OPT, cmdline.get_values(MMIO_WEAK_VARIABLE_OPT));
  }

  if(cmdline.isset(MMIO_WEAK_DEPTH_OPT))
  {
    options.set_option(
      MMIO_WEAK_DEPTH_OPT, cmdline.get_value(MMIO_WEAK_DEPTH_OPT));
  }

  if(cmdline.isset(MMIO_GATHER_OPT))
  {
    options.set_option(MMIO_GATHER_OPT, true);
  }

  if(cmdline.isset(MMIO_EARLY_ACK_OPT))
  {
    options.set_option(MMIO_EARLY_ACK_OPT, true);
  }
}

void nondet_volatile(goto_modelt &goto_model, const optionst &options)
{
  nondet_volatilet nv(goto_model, options);
  nv();
}
