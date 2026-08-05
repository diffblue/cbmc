/*******************************************************************\

Module: Program Transformation

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Lowering of full expressions for --evaluation-order-check
///
/// The C standard leaves the order of evaluation of the operands of most
/// operators, and of the arguments of a function call, unspecified (C11 6.5p3,
/// 6.5.2.2p10), and the choice need not be the same for two evaluations of the
/// same expression (C11 3.4.4). Goto conversion otherwise lowers each full
/// expression in one fixed order. With --evaluation-order-check, a full
/// expression is instead lowered as follows:
/// - Each side effect (function call, assignment, increment or decrement) is
///   an *event*. An event executes after the events within its operands, and
///   otherwise in any order relative to other events: with n events, there
///   are n rounds, and each event executes in a nondeterministically chosen
///   round that differs from the rounds of all other events and follows the
///   rounds of the events within its operands. This covers all orders of the
///   events that respect their dependencies while emitting each event at most
///   n times.
/// - Each maximal side-effect-free operand that reads memory is a *read*.
///   Its value is recorded as soon as the standard permits the read to
///   happen, and assertions check that the value is unchanged at the end of
///   each round until the read is consumed (by the event it is an operand of,
///   or by the value of the full expression). The assertions fail
///   exactly when evaluating the read at a different point permitted by the
///   standard yields a different value. As the read is evaluated at all these
///   points, the enabled undefined-behaviour checks (division by zero,
///   pointer checks etc.) apply at all of them.
///
/// Sub-expressions whose evaluation the standard sequences (&&, ||, ?:, the
/// comma operator) are executed as one event, within which the usual
/// lowering applies; full expressions within them are lowered as described
/// above. Full expressions that contain GCC statement expressions use the
/// fixed order, as their lowering may contain jumps out of the expression.
///
/// **Cost of the encoding.** Two sources of cost need to be distinguished:
/// - Code size: event e is emitted once for each round in which it may
///   execute, so n mutually unordered events yield n^2 copies, each of which
///   symex executes (inlining calls). Using temporaries or a different
///   sequential arrangement cannot avoid this: listing the event blocks of
///   any loop-free program in topological order yields a sequence that
///   contains every order of the events as a subsequence, and the shortest
///   sequence that contains all permutations of n symbols as subsequences
///   has length (1 - o(1)) n^2 (Kleitman and Kwiatkowski, 1976). The round
///   encoding is thus asymptotically optimal among sequential encodings.
/// - Search: when a property depends on the order (e.g., an overflow check
///   in code that updates the same global from several calls), the decision
///   procedure needs to refute all admissible orders. No encoding avoids
///   this; only reducing the set of orders does.
///
/// Measurements (total time in seconds of cbmc with MiniSat for one
/// expression `f0() + ... + f{n-1}()`; the fixed order, i.e., without
/// --evaluation-order-check, covers one order only and is listed for
/// reference):
///
/// | calls (n = 4 / 8 / 12)      | fixed order        | rounds             |
/// |-----------------------------|--------------------|--------------------|
/// | return a constant           | 0.02 / 0.02 / 0.02 | 0.02 / 0.07 / 0.18 |
/// | 50-iteration loop           | 0.03 / 0.05 / 0.06 | 0.08 / 0.30 / 0.72 |
/// | n = n * 3 + i on one global | 0.02 / 0.02 / 0.02 | 0.03 / 15.8 / >120 |
///
/// In the second row, each call runs a 50-iteration loop and writes a global
/// of its own; symex takes 0.48 s of the 0.72 s at n = 12 (31487 SSA steps,
/// growing quadratically). The calls that update one
/// global take 0.3 s at n = 12 when the default overflow checks are
/// disabled: the time is spent refuting an overflow in each of the 12!
/// orders.
///
/// The source code of mlkem-native and mldsa-native contains no expression
/// with two or more side effects whose order is not fixed, so neither cost
/// arises there; the remaining read assertions are mostly discharged by
/// symex (reads of local variables whose address is not taken cannot be
/// changed by a call).
///
/// **Alternatives that were considered.**
/// - CBMC's partial-order encoding of concurrency (Alglave, Kroening,
///   Tautschnig, CAV 2013), using one thread per event with its body in an
///   atomic section, emits each event once. Measured on the above, it was
///   slower than the round encoding in all cases (pure calls 0.39 s at
///   n = 12, the 50-iteration loop 1.06 s, the shared global timed out at
///   n = 8 where rounds take 15.8 s), as it orders every individual shared
///   read and write using clocks and read-from choices, whereas rounds only
///   order whole events. A specialised variant that executes each event once
///   and connects its inputs to the last write before its round would need
///   to be implemented in symex (the footprint of an event is not known
///   during goto conversion), including value sets for pointers that are
///   read by one event and written by another one; it would at most save
///   the symex time of the copies.
/// - Partial-order reduction: an event whose footprint (the memory it may
///   read and write, including its callees) does not conflict with any
///   unordered event or checked read commutes with all of them and need not
///   be reordered. Footprints require the whole program, which is only
///   available after linking.
/// - Checking non-interference instead of exploring orders, as Frama-C
///   does: assert that the footprints of unordered events are disjoint and
///   keep the fixed order. This costs linear code but reports conflicts
///   whose effects commute (two increments of a counter, the bookkeeping of
///   malloc).
/// - Bounding the reordering: let each event move by at most k positions,
///   yielding O(n * k) copies. This is incomplete, hence only suitable as an
///   opt-in for bug finding.

#include "goto_convert_class.h"

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <langapi/language_util.h>

#include "destructor.h"

#include <optional>
#include <set>
#include <utility>

/// The events of a sub-expression, and its reads that are not yet known to
/// be consumed by an event.
struct goto_convertt::evaluation_order_subtreet
{
  std::set<std::size_t> events;
  std::vector<std::size_t> pending_reads;

  void add(evaluation_order_subtreet &&other)
  {
    events.insert(other.events.begin(), other.events.end());
    pending_reads.insert(
      pending_reads.end(),
      other.pending_reads.begin(),
      other.pending_reads.end());
  }
};

/// Returns true if \p expr reads memory other than the \p temporaries
/// introduced while lowering the current full expression.
static bool reads_memory(
  const exprt &expr,
  const std::unordered_set<irep_idt> &temporaries);

/// Returns true if computing the address of \p object reads memory other
/// than the \p temporaries introduced while lowering the current full
/// expression.
static bool address_reads_memory(
  const exprt &object,
  const std::unordered_set<irep_idt> &temporaries)
{
  if(object.id() == ID_index)
  {
    const index_exprt &index_expr = to_index_expr(object);
    return address_reads_memory(index_expr.array(), temporaries) ||
           reads_memory(index_expr.index(), temporaries);
  }
  else if(object.id() == ID_member)
  {
    return address_reads_memory(to_member_expr(object).compound(), temporaries);
  }
  else if(object.id() == ID_dereference)
    return reads_memory(to_dereference_expr(object).pointer(), temporaries);
  else if(object.id() == ID_typecast)
    return address_reads_memory(to_typecast_expr(object).op(), temporaries);
  else if(
    object.id() == ID_symbol || object.is_constant() ||
    object.id() == ID_string_constant)
  {
    return false;
  }
  else
    return reads_memory(object, temporaries);
}

static bool
reads_memory(const exprt &expr, const std::unordered_set<irep_idt> &temporaries)
{
  if(expr.id() == ID_symbol)
  {
    return expr.type().id() != ID_code &&
           temporaries.find(to_symbol_expr(expr).identifier()) ==
             temporaries.end();
  }
  else if(expr.id() == ID_dereference)
    return true;
  else if(expr.id() == ID_address_of)
  {
    return address_reads_memory(to_address_of_expr(expr).object(), temporaries);
  }

  for(const auto &op : expr.operands())
  {
    if(reads_memory(op, temporaries))
      return true;
  }

  return false;
}

/// The events and reads of one full expression.
struct goto_convertt::evaluation_order_regiont
{
  struct eventt
  {
    /// The lowering of the event.
    goto_programt code;
    /// The events that must execute before this one as they are part of its
    /// operands; transitively closed.
    std::set<std::size_t> predecessors;
  };

  struct readt
  {
    /// The side-effect-free expression that reads memory.
    exprt expr;
    /// The events whose results the read uses, which hence must execute
    /// before it.
    std::set<std::size_t> dependencies;
    /// The event that the read is an operand of, if any; otherwise its value
    /// is part of the value of the full expression.
    std::optional<std::size_t> consumer;
  };

  std::vector<eventt> events;
  std::vector<readt> reads;
  std::list<irep_idt> temporaries;
  std::unordered_set<irep_idt> temporary_identifiers;

  /// Returns true if \p expr is a read: a side-effect-free expression of a
  /// type that supports comparison for equality, which reads memory that may
  /// be modified by the events of the full expression.
  bool is_read(const exprt &expr) const
  {
    const irep_idt &type_id = expr.type().id();
    if(
      type_id != ID_signedbv && type_id != ID_unsignedbv && type_id != ID_bv &&
      type_id != ID_bool && type_id != ID_c_bool && type_id != ID_pointer &&
      type_id != ID_floatbv && type_id != ID_fixedbv && type_id != ID_c_enum &&
      type_id != ID_c_enum_tag && type_id != ID_c_bit_field)
    {
      return false;
    }

    // Reading volatile objects twice need not yield the same value.
    return !has_subexpr(expr, ID_side_effect) &&
           !has_subexpr(
             expr,
             [](const exprt &e) { return e.type().get_bool(ID_C_volatile); }) &&
           reads_memory(expr, temporary_identifiers);
  }

  void add_read(
    exprt expr,
    std::set<std::size_t> dependencies,
    evaluation_order_subtreet &subtree)
  {
    subtree.pending_reads.push_back(reads.size());
    reads.push_back({std::move(expr), std::move(dependencies), {}});
  }
};

/// Returns true if \p expr is lowered as a whole by `clean_expr` even with
/// --evaluation-order-check: either the standard sequences the evaluation of
/// its operands, or it is an address computation.
static bool is_lowered_as_a_whole(const exprt &expr)
{
  if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies ||
    expr.id() == ID_if || expr.id() == ID_comma || expr.id() == ID_forall ||
    expr.id() == ID_exists || expr.id() == ID_address_of)
  {
    return true;
  }

  if(expr.id() == ID_side_effect)
  {
    const irep_idt &statement = to_side_effect_expr(expr).get_statement();
    return statement == ID_gcc_conditional_expression ||
           statement == ID_statement_expression;
  }

  return false;
}

static bool contains_statement_expression(const exprt &expr)
{
  return has_subexpr(
    expr,
    [](const exprt &e)
    {
      return e.id() == ID_side_effect &&
             to_side_effect_expr(e).get_statement() == ID_statement_expression;
    });
}

/// Returns true if \p expr contains a side effect that results in an event,
/// i.e., a side effect other than a nondeterministic choice.
static bool has_event(const exprt &expr)
{
  return has_subexpr(
    expr,
    [](const exprt &e)
    {
      if(e.id() != ID_side_effect)
        return e.id() == ID_comma || e.id() == ID_compound_literal;
      const irep_idt &statement = to_side_effect_expr(e).get_statement();
      return statement != ID_nondet && statement != ID_skip;
    });
}

/// Returns true if --evaluation-order-check applies to expressions in \p mode
/// at the location of \p expr. The models of the built-in library are not
/// checked.
bool goto_convertt::evaluation_order_check_enabled(
  const exprt &expr,
  const irep_idt &mode) const
{
  if(
    !config.ansi_c.evaluation_order_check || mode != ID_C ||
    evaluation_order_check_suspended)
  {
    return false;
  }

  const std::string &file = id2string(expr.find_source_location().get_file());
  return !has_prefix(file, "<builtin-library") &&
         !has_prefix(file, "<built-in-");
}

/// Returns true if the full expression \p expr is to be lowered by
/// \ref goto_convertt::clean_expr_evaluation_order.
bool goto_convertt::use_evaluation_order_check(
  const exprt &expr,
  const irep_idt &mode) const
{
  return needs_cleaning(expr) && !is_lowered_as_a_whole(expr) &&
         evaluation_order_check_enabled(expr, mode) &&
         !contains_statement_expression(expr);
}

/// Returns true if the operands of a call of \p function with \p arguments
/// are to be lowered by \ref
/// goto_convertt::clean_function_call_operands_evaluation_order.
bool goto_convertt::use_evaluation_order_check(
  const exprt &function,
  const exprt::operandst &arguments,
  const irep_idt &mode) const
{
  if(!evaluation_order_check_enabled(function, mode))
    return false;

  bool needs_cleaning_any = needs_cleaning(function);
  for(const auto &argument : arguments)
  {
    if(contains_statement_expression(argument))
      return false;
    needs_cleaning_any = needs_cleaning_any || needs_cleaning(argument);
  }

  return needs_cleaning_any && !contains_statement_expression(function);
}

/// Returns true if the assignment \p code is to be lowered by \ref
/// goto_convertt::convert_assign_evaluation_order. The evaluations of its
/// left-hand side and right-hand side are unsequenced, which matters when
/// either of them has side effects and the other one reads memory.
bool goto_convertt::use_evaluation_order_check(
  const code_assignt &code,
  const irep_idt &mode) const
{
  if(!evaluation_order_check_enabled(code, mode))
    return false;

  const exprt &lhs = code.lhs();
  const exprt &rhs = code.rhs();

  if(!has_event(lhs) && (!has_event(rhs) || !address_reads_memory(lhs, {})))
  {
    return false;
  }

  return !contains_statement_expression(lhs) &&
         !contains_statement_expression(rhs);
}

/// Lower the full expression \p expr for --evaluation-order-check.
/// \param expr: expression to lower; replaced by its side-effect-free
///   residual
/// \param mode: language mode
/// \param result_is_used: whether the value of \p expr is used
/// \return the lowering and the temporaries introduced
goto_convertt::clean_expr_resultt goto_convertt::clean_expr_evaluation_order(
  exprt &expr,
  const irep_idt &mode,
  bool result_is_used)
{
  const source_locationt source_location = expr.find_source_location();

  evaluation_order_regiont region;
  evaluation_order_subtreet subtree;
  collect_evaluation_order(expr, mode, result_is_used, region, subtree);

  return emit_evaluation_order_region(region, source_location, mode);
}

/// Lower the function operand and the arguments of a function call for
/// --evaluation-order-check. The reads among them are consumed by the call.
goto_convertt::clean_expr_resultt
goto_convertt::clean_function_call_operands_evaluation_order(
  exprt &function,
  exprt::operandst &arguments,
  const irep_idt &mode)
{
  const source_locationt source_location = function.find_source_location();

  evaluation_order_regiont region;
  evaluation_order_subtreet subtree;

  collect_evaluation_order_call_operands(
    function, arguments, mode, region, subtree);

  return emit_evaluation_order_region(region, source_location, mode);
}

/// Lower the assignment \p code for --evaluation-order-check, treating it as
/// one full expression.
void goto_convertt::convert_assign_evaluation_order(
  const code_assignt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt assignment =
    side_effect_expr_assignt{code.lhs(), code.rhs(), code.source_location()};

  clean_expr_resultt side_effects =
    clean_expr_evaluation_order(assignment, mode, false);
  dest.destructive_append(side_effects.side_effects);
  destruct_locals(side_effects.temporaries, dest, ns);
}

/// Collect the events and reads of \p expr, which needs cleaning, into
/// \p region, lowering the side effects of \p expr.
/// \param expr: expression to lower; replaced by its side-effect-free
///   residual
/// \param mode: language mode
/// \param result_is_used: whether the value of \p expr is used
/// \param region: the events and reads of the full expression
/// \param [out] subtree: the events and pending reads of \p expr are added
///   to this
void goto_convertt::collect_evaluation_order(
  exprt &expr,
  const irep_idt &mode,
  bool result_is_used,
  evaluation_order_regiont &region,
  evaluation_order_subtreet &subtree)
{
  PRECONDITION(needs_cleaning(expr));

  if(is_lowered_as_a_whole(expr))
  {
    evaluation_order_subtreet whole;
    add_evaluation_order_event(
      clean_expr(expr, mode, result_is_used), region, {}, whole);

    // The value of the expression may read memory (e.g., the last operand
    // of a comma expression), which happens after the event.
    if(!whole.events.empty() && region.is_read(expr))
      region.add_read(expr, whole.events, whole);

    subtree.add(std::move(whole));
    return;
  }

  if(expr.id() == ID_typecast)
  {
    exprt &op = to_typecast_expr(expr).op();
    collect_evaluation_order(op, mode, result_is_used, region, subtree);
    if(op.is_nil())
      expr.make_nil();
    return;
  }

  evaluation_order_subtreet operands;

  if(expr.id() == ID_side_effect)
  {
    side_effect_exprt &side_effect = to_side_effect_expr(expr);
    const irep_idt &statement = side_effect.get_statement();

    if(statement == ID_function_call)
    {
      collect_evaluation_order_call_operands(
        to_side_effect_expr_function_call(side_effect).function(),
        to_side_effect_expr_function_call(side_effect).arguments(),
        mode,
        region,
        operands);
    }
    else if(
      statement == ID_assign || statement == ID_assign_plus ||
      statement == ID_assign_minus || statement == ID_assign_mult ||
      statement == ID_assign_div || statement == ID_assign_bitor ||
      statement == ID_assign_bitxor || statement == ID_assign_bitand ||
      statement == ID_assign_lshr || statement == ID_assign_ashr ||
      statement == ID_assign_shl || statement == ID_assign_mod)
    {
      PRECONDITION(side_effect.operands().size() == 2);
      exprt &lhs = side_effect.operands()[0];
      exprt &rhs = side_effect.operands()[1];
      collect_evaluation_order_lvalue(lhs, mode, region, operands);
      // compound assignments read the left-hand side
      if(statement != ID_assign && !needs_cleaning(lhs) && region.is_read(lhs))
        region.add_read(lhs, {}, operands);
      if(
        statement == ID_assign && rhs.id() == ID_side_effect &&
        to_side_effect_expr(rhs).get_statement() == ID_function_call &&
        !address_reads_memory(lhs, region.temporary_identifiers))
      {
        // clean_expr assigns the result of the call directly, which makes
        // the call part of the assignment's event; this is only done when
        // computing the address of the left-hand side reads no memory, which
        // the call could otherwise modify
        collect_evaluation_order_call_operands(
          to_side_effect_expr_function_call(rhs).function(),
          to_side_effect_expr_function_call(rhs).arguments(),
          mode,
          region,
          operands);
      }
      else
        collect_evaluation_order_operand(rhs, mode, region, operands);
    }
    else if(
      statement == ID_postincrement || statement == ID_postdecrement ||
      statement == ID_preincrement || statement == ID_predecrement)
    {
      PRECONDITION(side_effect.operands().size() == 1);
      exprt &op = side_effect.operands()[0];
      collect_evaluation_order_lvalue(op, mode, region, operands);
      if(!needs_cleaning(op) && region.is_read(op))
        region.add_read(op, {}, operands);
    }
    else
    {
      Forall_operands(it, side_effect)
        collect_evaluation_order_operand(*it, mode, region, operands);
    }

    // All operands are now free of side effects: lower the side effect itself
    // as clean_expr does without --evaluation-order-check.
    clean_expr_resultt lowered;
    {
      const bool suspended =
        std::exchange(evaluation_order_check_suspended, true);
      lowered = clean_expr(expr, mode, result_is_used);
      evaluation_order_check_suspended = suspended;
    }

    // The value of an assignment, or of a pre-increment or pre-decrement, is
    // the value stored (C11 6.5.16p3), which the lowering otherwise re-reads
    // from the left-hand side after all events have executed. Record it as
    // part of the event so that other events cannot affect it.
    for(const auto &identifier : lowered.temporaries)
      region.temporary_identifiers.insert(identifier);
    if(result_is_used && expr.is_not_nil() && region.is_read(expr))
    {
      lowered.add_temporary(make_temp_symbol(
        expr, "eval_order_result", lowered.side_effects, mode));
    }

    add_evaluation_order_event(
      std::move(lowered), region, std::move(operands), subtree);
    return;
  }

  Forall_operands(it, expr)
    collect_evaluation_order_operand(*it, mode, region, operands);

  if(expr.id() == ID_compound_literal)
  {
    // This is simply replaced by the literal, as in clean_expr.
    DATA_INVARIANT(
      expr.operands().size() == 1, "ID_compound_literal has a single operand");
    expr = to_unary_expr(expr).op();
  }
  else if(
    (expr.id() == ID_index || expr.id() == ID_dereference ||
     expr.id() == ID_member) &&
    !operands.events.empty() && region.is_read(expr))
  {
    // A read of memory whose address depends on the results of events, as
    // in a[i++] or *f().
    region.add_read(expr, operands.events, operands);
  }

  subtree.add(std::move(operands));
}

/// Collect the events and reads of the \p function operand and of the
/// \p arguments of a function call, which are evaluated in an unspecified
/// order.
void goto_convertt::collect_evaluation_order_call_operands(
  exprt &function,
  exprt::operandst &arguments,
  const irep_idt &mode,
  evaluation_order_regiont &region,
  evaluation_order_subtreet &subtree)
{
  if(function.id() == ID_dereference)
  {
    collect_evaluation_order_operand(
      to_dereference_expr(function).pointer(), mode, region, subtree);
  }
  else if(needs_cleaning(function))
    collect_evaluation_order(function, mode, true, region, subtree);

  for(auto &argument : arguments)
    collect_evaluation_order_operand(argument, mode, region, subtree);
}

/// Collect the events and reads of \p operand, which is evaluated as an
/// operand of an expression that needs cleaning.
void goto_convertt::collect_evaluation_order_operand(
  exprt &operand,
  const irep_idt &mode,
  evaluation_order_regiont &region,
  evaluation_order_subtreet &subtree)
{
  if(needs_cleaning(operand))
    collect_evaluation_order(operand, mode, true, region, subtree);
  else if(region.is_read(operand))
    region.add_read(operand, {}, subtree);
}

/// Collect the events and reads of the address computation of the lvalue
/// \p lvalue.
void goto_convertt::collect_evaluation_order_lvalue(
  exprt &lvalue,
  const irep_idt &mode,
  evaluation_order_regiont &region,
  evaluation_order_subtreet &subtree)
{
  if(lvalue.id() == ID_index)
  {
    index_exprt &index_expr = to_index_expr(lvalue);
    collect_evaluation_order_lvalue(index_expr.array(), mode, region, subtree);
    collect_evaluation_order_operand(index_expr.index(), mode, region, subtree);
  }
  else if(lvalue.id() == ID_dereference)
  {
    collect_evaluation_order_operand(
      to_dereference_expr(lvalue).pointer(), mode, region, subtree);
  }
  else if(lvalue.id() == ID_member)
  {
    collect_evaluation_order_lvalue(
      to_member_expr(lvalue).compound(), mode, region, subtree);
  }
  else if(lvalue.id() == ID_typecast)
  {
    collect_evaluation_order_lvalue(
      to_typecast_expr(lvalue).op(), mode, region, subtree);
  }
  else if(needs_cleaning(lvalue))
    collect_evaluation_order(lvalue, mode, true, region, subtree);
}

/// Record the lowering \p lowered of a side effect as an event of \p region
/// that executes after the events of its \p operands, which consumes the
/// pending reads of its \p operands.
void goto_convertt::add_evaluation_order_event(
  clean_expr_resultt &&lowered,
  evaluation_order_regiont &region,
  evaluation_order_subtreet &&operands,
  evaluation_order_subtreet &subtree)
{
  for(const auto &identifier : lowered.temporaries)
    region.temporary_identifiers.insert(identifier);
  region.temporaries.splice(region.temporaries.begin(), lowered.temporaries);

  if(lowered.side_effects.instructions.empty())
  {
    // e.g., a nondeterministic choice
    subtree.add(std::move(operands));
    return;
  }

  const std::size_t event = region.events.size();
  for(const std::size_t read : operands.pending_reads)
    region.reads[read].consumer = event;

  region.events.push_back({std::move(lowered.side_effects), operands.events});

  subtree.events.insert(operands.events.begin(), operands.events.end());
  subtree.events.insert(event);
}

/// Emit the events of \p region in a nondeterministically chosen order that
/// respects their dependencies, together with the snapshots of and the
/// assertions about its reads.
/// \param region: the events and reads of a full expression
/// \param source_location: location of the full expression
/// \param mode: language mode
/// \return the lowering of the full expression and the temporaries
///   introduced
goto_convertt::clean_expr_resultt goto_convertt::emit_evaluation_order_region(
  evaluation_order_regiont &region,
  const source_locationt &source_location,
  const irep_idt &mode)
{
  clean_expr_resultt result;
  result.temporaries.splice(result.temporaries.begin(), region.temporaries);

  auto &events = region.events;
  const std::size_t n = events.size();
  if(n == 0)
    return result;

  // Event e can only execute in rounds earliest[e] to latest[e], as all of
  // its predecessors execute before it and all of its successors after it.
  std::vector<std::size_t> number_of_successors(n, 0);
  for(const auto &event : events)
  {
    for(const std::size_t predecessor : event.predecessors)
      ++number_of_successors[predecessor];
  }
  std::vector<std::size_t> earliest(n), latest(n);
  for(std::size_t e = 0; e < n; ++e)
  {
    earliest[e] = events[e].predecessors.size();
    latest[e] = n - 1 - number_of_successors[e];
    INVARIANT(earliest[e] <= latest[e], "events must form a partial order");
  }

  // A read needs to be checked if an event may execute after the read could
  // first happen and before the read is consumed.
  const auto may_change_read =
    [&events](const evaluation_order_regiont::readt &read, std::size_t e)
  {
    if(read.dependencies.find(e) != read.dependencies.end())
      return false;
    for(const std::size_t dependency : read.dependencies)
    {
      if(events[dependency].predecessors.count(e) != 0)
        return false;
    }
    return !read.consumer.has_value() ||
           (e != *read.consumer &&
            events[e].predecessors.count(*read.consumer) == 0);
  };

  std::vector<std::size_t> checked_reads;
  for(std::size_t r = 0; r < region.reads.size(); ++r)
  {
    for(std::size_t e = 0; e < n; ++e)
    {
      if(may_change_read(region.reads[r], e))
      {
        checked_reads.push_back(r);
        break;
      }
    }
  }

  goto_programt &dest = result.side_effects;

  bool order_is_fixed = true;
  for(std::size_t e = 0; e < n; ++e)
    order_is_fixed = order_is_fixed && earliest[e] == latest[e];

  if(order_is_fixed && checked_reads.empty())
  {
    std::vector<std::size_t> order(n);
    for(std::size_t e = 0; e < n; ++e)
      order[earliest[e]] = e;
    for(const std::size_t e : order)
      dest.destructive_append(events[e].code);
    return result;
  }

  // Hoist declarations out of the events so that the events can be emitted
  // several times, under disjoint guards. The declarations are replaced by
  // skips as they may be jump targets.
  for(auto &event : events)
  {
    for(auto &instruction : event.code.instructions)
    {
      if(instruction.is_decl())
      {
        dest.add(goto_programt::instructiont{instruction});
        instruction.turn_into_skip();
      }
    }
  }

  const auto new_temporary =
    [&](const typet &type, const std::string &suffix) -> symbol_exprt
  {
    const symbolt &symbol =
      new_tmp_symbol(type, "eval_order_" + suffix, dest, source_location, mode);
    result.add_temporary(symbol.name);
    return symbol.symbol_expr();
  };

  // Each event executes in a nondeterministically chosen round, which is
  // distinct from the rounds of all other events and later than the rounds
  // of its predecessors. Choosing the round per event (rather than the event
  // per round) makes it evident to the decision procedure that each event
  // executes exactly once. The type of rounds needs to represent n, which is
  // used to describe the state after the last round.
  const unsignedbv_typet round_type{address_bits(n + 1)};
  std::vector<exprt> rounds(n);
  exprt::operandst constraints;
  for(std::size_t e = 0; e < n; ++e)
  {
    if(earliest[e] == latest[e])
      rounds[e] = from_integer(earliest[e], round_type);
    else
    {
      const symbol_exprt round = new_temporary(round_type, "round");
      dest.add(goto_programt::make_assignment(
        round,
        side_effect_expr_nondett{round_type, source_location},
        source_location));
      constraints.push_back(binary_relation_exprt{
        round, ID_ge, from_integer(earliest[e], round_type)});
      constraints.push_back(binary_relation_exprt{
        round, ID_le, from_integer(latest[e], round_type)});
      rounds[e] = round;
    }
  }
  for(std::size_t e = 0; e < n; ++e)
  {
    for(const std::size_t predecessor : events[e].predecessors)
    {
      constraints.push_back(
        binary_relation_exprt{rounds[predecessor], ID_lt, rounds[e]});
    }
    for(std::size_t other = e + 1; other < n; ++other)
    {
      if(earliest[other] <= latest[e] && earliest[e] <= latest[other])
        constraints.push_back(notequal_exprt{rounds[e], rounds[other]});
    }
  }
  const exprt constraint = simplify_expr(conjunction(constraints), ns);
  if(constraint != true)
  {
    dest.add(goto_programt::make_assumption(constraint, source_location));
  }

  // Whether event e has executed once the first rounds_completed rounds have
  // completed.
  const auto executed =
    [&](std::size_t e, std::size_t rounds_completed) -> exprt
  {
    if(rounds_completed <= earliest[e])
      return false_exprt{};
    else if(rounds_completed > latest[e])
      return true_exprt{};
    else
    {
      return binary_relation_exprt{
        rounds[e], ID_lt, from_integer(rounds_completed, round_type)};
    }
  };

  const auto all_executed =
    [&](const std::set<std::size_t> &dependencies, std::size_t rounds_completed)
  {
    exprt::operandst conjuncts;
    for(const std::size_t dependency : dependencies)
      conjuncts.push_back(executed(dependency, rounds_completed));
    return simplify_expr(conjunction(conjuncts), ns);
  };

  // Emit "if(guard) { body }".
  const auto emit_guarded = [&](const exprt &guard, goto_programt &&body)
  {
    if(guard == false)
      return;
    if(guard == true)
    {
      dest.destructive_append(body);
      return;
    }
    goto_programt skip;
    const auto skip_target =
      skip.add(goto_programt::make_skip(source_location));
    dest.add(goto_programt::make_goto(
      skip_target, boolean_negate(guard), source_location));
    dest.destructive_append(body);
    dest.destructive_append(skip);
  };

  // Reads without dependencies may happen right away; the values of reads
  // with dependencies are recorded once their dependencies have executed.
  std::vector<std::pair<std::size_t, symbol_exprt>> snapshots;
  for(const std::size_t r : checked_reads)
  {
    const auto &read = region.reads[r];
    snapshots.emplace_back(r, new_temporary(read.expr.type(), "value"));
    if(read.dependencies.empty())
    {
      dest.add(goto_programt::make_assignment(
        snapshots.back().second, read.expr, source_location));
    }
  }

  for(std::size_t round = 0; round < n; ++round)
  {
    for(std::size_t e = 0; e < n; ++e)
    {
      if(earliest[e] <= round && round <= latest[e])
      {
        goto_programt copy;
        copy.copy_from(events[e].code);
        emit_guarded(
          simplify_expr(
            equal_exprt{rounds[e], from_integer(round, round_type)}, ns),
          std::move(copy));
      }
    }

    const std::size_t rounds_completed = round + 1;

    for(const auto &[r, value] : snapshots)
    {
      const auto &read = region.reads[r];

      if(!read.dependencies.empty())
      {
        // record the value in the round in which the last dependency
        // executes
        goto_programt body;
        body.add(
          goto_programt::make_assignment(value, read.expr, source_location));
        emit_guarded(
          simplify_expr(
            and_exprt{
              all_executed(read.dependencies, rounds_completed),
              boolean_negate(all_executed(read.dependencies, round))},
            ns),
          std::move(body));
      }

      // check that the value is unchanged while the read has not been
      // consumed
      exprt::operandst conjuncts;
      conjuncts.push_back(all_executed(read.dependencies, rounds_completed));
      if(read.consumer.has_value())
      {
        conjuncts.push_back(
          boolean_negate(executed(*read.consumer, rounds_completed)));
      }

      source_locationt annotated_location = read.expr.find_source_location();
      if(annotated_location.get_file().empty())
        annotated_location = source_location;
      annotated_location.set_property_class("evaluation-order");
      annotated_location.set_comment(
        "value of " + from_expr(ns, mode, read.expr) +
        " is independent of evaluation order");
      goto_programt body;
      body.add(goto_programt::make_assertion(
        equal_exprt{value, read.expr}, annotated_location));
      emit_guarded(simplify_expr(conjunction(conjuncts), ns), std::move(body));
    }
  }

  return result;
}
