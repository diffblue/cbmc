/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "symex_assign.h"

#include "goto_symex.h"
#include "goto_symex_state.h"
#include <util/byte_operators.h>
#include <util/expr_util.h>
#include <util/format_expr.h>

// We can either use with_exprt or update_exprt when building expressions that
// modify components of an array or a struct. Set USE_UPDATE to use
// update_exprt.
// #define USE_UPDATE

expr_skeletont expr_skeletont::remove_op0(exprt e)
{
  PRECONDITION(e.id() != ID_symbol);
  PRECONDITION(e.operands().size() >= 1);
  e.op0().make_nil();
  return expr_skeletont{std::move(e)};
}

exprt expr_skeletont::apply(exprt expr) const
{
  PRECONDITION(skeleton.id() != ID_symbol);
  exprt result = skeleton;
  exprt *p = &result;

  while(p->is_not_nil())
  {
    INVARIANT(
      p->id() != ID_symbol,
      "expected pointed-to expression not to be a symbol");
    INVARIANT(
      p->operands().size() >= 1,
      "expected pointed-to expression to have at least one operand");
    p = &p->op0();
  }

  INVARIANT(p->is_nil(), "expected pointed-to expression to be nil");

  *p = std::move(expr);
  return result;
}

expr_skeletont expr_skeletont::compose(expr_skeletont other) const
{
  return expr_skeletont(apply(other.skeleton));
}

void symex_assignt::assign_rec(
  const assignmentt<exprt> &assignment,
  exprt::operandst &guard)
{
  if(
    assignment.lhs.id() == ID_symbol &&
    assignment.lhs.get_bool(ID_C_SSA_symbol))
  {
    assign_symbol(replace_lhs(assignment, to_ssa_expr(assignment.lhs)), guard);
  }
  else if(assignment.lhs.id() == ID_index)
    assign_array(replace_lhs(assignment, to_index_expr(assignment.lhs)), guard);
  else if(assignment.lhs.id() == ID_member)
  {
    const typet &type = to_member_expr(assignment.lhs).struct_op().type();
    if(type.id() == ID_struct || type.id() == ID_struct_tag)
    {
      assign_struct_member(
        replace_lhs(assignment, to_member_expr(assignment.lhs)), guard);
    }
    else if(type.id() == ID_union || type.id() == ID_union_tag)
    {
      // should have been replaced by byte_extract
      throw unsupported_operation_exceptiont(
        "symex_assign_rec: unexpected assignment to union member");
    }
    else
      throw unsupported_operation_exceptiont(
        "symex_assign_rec: unexpected assignment to member of `" +
        type.id_string() + "'");
  }
  else if(assignment.lhs.id() == ID_if)
    assign_if(replace_lhs(assignment, to_if_expr(assignment.lhs)), guard);
  else if(assignment.lhs.id() == ID_typecast)
    assign_typecast(
      replace_lhs(assignment, to_typecast_expr(assignment.lhs)), guard);
  else if(
    assignment.lhs.id() == ID_string_constant ||
    assignment.lhs.id() == ID_null_object ||
    assignment.lhs.id() == "zero_string" ||
    assignment.lhs.id() == "is_zero_string" ||
    assignment.lhs.id() == "zero_string_length")
  {
    // ignore
  }
  else if(
    assignment.lhs.id() == ID_byte_extract_little_endian ||
    assignment.lhs.id() == ID_byte_extract_big_endian)
  {
    assign_byte_extract(
      replace_lhs(assignment, to_byte_extract_expr(assignment.lhs)), guard);
  }
  else if(assignment.lhs.id() == ID_complex_real)
  {
    // this is stuff like __real__ x = 1;
    const complex_real_exprt &complex_real_expr =
      to_complex_real_expr(assignment.lhs);

    const complex_imag_exprt complex_imag_expr(complex_real_expr.op());
    assignmentt<exprt> new_assignment;
    new_assignment.rhs =
      complex_exprt{assignment.rhs,
                    complex_imag_expr,
                    to_complex_type(complex_real_expr.op().type())};
    new_assignment.lhs = complex_real_expr.op();
    new_assignment.original_lhs_skeleton = assignment.original_lhs_skeleton;
    assign_rec(new_assignment, guard);
  }
  else if(assignment.lhs.id() == ID_complex_imag)
  {
    const complex_imag_exprt &complex_imag_expr =
      to_complex_imag_expr(assignment.lhs);

    const complex_real_exprt complex_real_expr(complex_imag_expr.op());
    assignmentt<exprt> new_assignment;
    new_assignment.rhs =
      complex_exprt{complex_real_expr,
                    assignment.rhs,
                    to_complex_type(complex_imag_expr.op().type())};
    new_assignment.lhs = complex_imag_expr.op();
    new_assignment.original_lhs_skeleton = assignment.original_lhs_skeleton;
    assign_rec(new_assignment, guard);
  }
  else
    throw unsupported_operation_exceptiont(
      "assignment to `" + assignment.lhs.id_string() + "' not handled");
}

/// Replace "with" (or "update") expressions in the right-hand side of
/// \p assignment by their update values and move the index or member to the
/// left-hand side of \p assignment. This effectively undoes the work that
/// \ref symex_assignt::assign_array and
/// \ref symex_assignt::assign_struct_member have done, but now making use
/// of the index/member that may only be known after renaming to L2 has taken
/// place.
/// \param [in, out] state: symbolic execution state to perform renaming
/// \param assignment: an assignment to rewrite
/// \param ns: namespace
/// \return the updated assignment
static assignmentt<ssa_exprt> rewrite_with_to_field_symbols(
  goto_symext::statet &state,
  assignmentt<ssa_exprt> assignment,
  const namespacet &ns)
{
  exprt &ssa_rhs = assignment.rhs;
  ssa_exprt &lhs_mod = assignment.lhs;
#ifdef USE_UPDATE
  while(ssa_rhs.id() == ID_update &&
        to_update_expr(ssa_rhs).designator().size() == 1 &&
        (assignment.lhs_mod.type().id() == ID_array ||
         assignment.lhs_mod.type().id() == ID_struct ||
         assignment.lhs_mod.type().id() == ID_struct_tag))
  {
    exprt field_sensitive_lhs;
    const update_exprt &update = to_update_expr(ssa_rhs);
    PRECONDITION(update.designator().size() == 1);
    const exprt &designator = update.designator().front();

    if(assignment.lhs_mod.type().id() == ID_array)
    {
      field_sensitive_lhs = index_exprt(
        assignment.lhs_mod, to_index_designator(designator).index());
    }
    else
    {
      field_sensitive_lhs = member_exprt(
        assignment.lhs_mod,
        to_member_designator(designator).get_component_name(),
        update.new_value().type());
    }

    state.field_sensitivity.apply(state, field_sensitive_lhs, true);

    if(field_sensitive_lhs.id() != ID_symbol)
      break;

    ssa_rhs = update.new_value();
    lhs_mod = to_ssa_expr(field_sensitive_lhs);
  }
#else
  while(ssa_rhs.id() == ID_with &&
        to_with_expr(ssa_rhs).operands().size() == 3 &&
        (lhs_mod.type().id() == ID_array || lhs_mod.type().id() == ID_struct ||
         lhs_mod.type().id() == ID_struct_tag))
  {
    exprt field_sensitive_lhs;
    const with_exprt &with_expr = to_with_expr(ssa_rhs);

    if(lhs_mod.type().id() == ID_array)
    {
      field_sensitive_lhs = index_exprt(lhs_mod, with_expr.where());
    }
    else
    {
      field_sensitive_lhs = member_exprt(
        lhs_mod,
        with_expr.where().get(ID_component_name),
        with_expr.new_value().type());
    }

    field_sensitive_lhs = state.field_sensitivity.apply(
      ns, state, std::move(field_sensitive_lhs), true);

    if(field_sensitive_lhs.id() != ID_symbol)
      break;

    ssa_rhs = with_expr.new_value();
    lhs_mod = to_ssa_expr(field_sensitive_lhs);
  }
#endif
  return assignment;
}

/// Replace byte-update operations that only affect individual fields of an
/// expression by assignments to just those fields. May generate "with" (or
/// "update") expressions, which \ref rewrite_with_to_field_symbols will then
/// take care of.
/// \param [in, out] state: symbolic execution state to perform renaming
/// \param assignment: assignment to transform
/// \param ns: namespace
/// \param do_simplify: set to true if, and only if, simplification is enabled
/// \return updated assignment
static assignmentt<ssa_exprt> shift_indexed_access_to_lhs(
  goto_symext::statet &state,
  assignmentt<ssa_exprt> assignment,
  const namespacet &ns,
  bool do_simplify)
{
  exprt &ssa_rhs = assignment.rhs;
  ssa_exprt &lhs_mod = assignment.lhs;
  if(
    ssa_rhs.id() == ID_byte_update_little_endian ||
    ssa_rhs.id() == ID_byte_update_big_endian)
  {
    const byte_update_exprt &byte_update = to_byte_update_expr(ssa_rhs);
    exprt byte_extract = byte_extract_exprt(
      byte_update.id() == ID_byte_update_big_endian
        ? ID_byte_extract_big_endian
        : ID_byte_extract_little_endian,
      lhs_mod,
      byte_update.offset(),
      byte_update.value().type());
    if(do_simplify)
      simplify(byte_extract, ns);

    if(byte_extract.id() == ID_symbol)
    {
      return assignmentt<ssa_exprt>{assignment.original_lhs_skeleton,
                                    to_ssa_expr(byte_extract),
                                    byte_update.value()};
    }
    else if(byte_extract.id() == ID_index || byte_extract.id() == ID_member)
    {
      ssa_rhs = byte_update.value();

      while(byte_extract.id() == ID_index || byte_extract.id() == ID_member)
      {
        if(byte_extract.id() == ID_index)
        {
          index_exprt &idx = to_index_expr(byte_extract);

#ifdef USE_UPDATE
          update_exprt new_rhs{idx.array(), exprt{}, ssa_rhs};
          new_rhs.designator().push_back(index_designatort{idx.index()});
#else
          with_exprt new_rhs{idx.array(), idx.index(), ssa_rhs};
#endif

          ssa_rhs = new_rhs;
          byte_extract = idx.array();
        }
        else
        {
          member_exprt &member = to_member_expr(byte_extract);
          const irep_idt &component_name = member.get_component_name();

#ifdef USE_UPDATE
          update_exprt new_rhs{member.compound(), exprt{}, ssa_rhs};
          new_rhs.designator().push_back(member_designatort{component_name});
#else
          with_exprt new_rhs(member.compound(), exprt(ID_member_name), ssa_rhs);
          new_rhs.where().set(ID_component_name, component_name);
#endif

          ssa_rhs = new_rhs;
          byte_extract = member.compound();
        }
      }

      // We may have shifted the previous lhs into the rhs; as the lhs is only
      // L1-renamed, we need to rename again.
      return assignmentt<ssa_exprt>{assignment.original_lhs_skeleton,
                                    to_ssa_expr(byte_extract),
                                    state.rename(std::move(ssa_rhs), ns).get()};
    }
  }
  return assignment;
}

/// Assign a struct expression to a symbol. If \ref symex_assignt::assign_symbol
/// was used then we would assign the whole symbol, before extracting its
/// components, with results like
/// `x = {1, 2}; x..field1 = x.field1; x..field2 = x.field2;`
/// This abbreviates the process, directly producing
/// `x..field1 = 1; x..field2 = 2;`
/// \param lhs: symbol to assign (already renamed to L1)
/// \param full_lhs: expression skeleton corresponding to \p lhs, to be included
///   in the result trace
/// \param rhs: struct expression to assign to \p lhs
/// \param guard: guard conjuncts that must hold for this assignment to be made
void symex_assignt::assign_from_struct(
  const ssa_exprt &lhs, // L1
  const expr_skeletont &full_lhs,
  const struct_exprt &rhs,
  const exprt::operandst &guard)
{
  const auto &components = to_struct_type(ns.follow(lhs.type())).components();
  PRECONDITION(rhs.operands().size() == components.size());

  for(const auto &comp_rhs : make_range(components).zip(rhs.operands()))
  {
    const auto &comp = comp_rhs.first;
    const exprt lhs_field = state.field_sensitivity.apply(
      ns, state, member_exprt{lhs, comp.get_name(), comp.type()}, true);
    INVARIANT(
      lhs_field.id() == ID_symbol,
      "member of symbol should be susceptible to field-sensitivity");

    assign_symbol(
      assignmentt<ssa_exprt>{full_lhs, to_ssa_expr(lhs_field), comp_rhs.second},
      guard);
  }
}

void symex_assignt::assign_non_struct_symbol(
  assignmentt<ssa_exprt> assignment, // L1
  const exprt::operandst &guard)
{
  assignment.rhs =
    state
      .rename(
        // put assignment guard into the assignment.rhs
        guard.empty() ? assignment.rhs
                      : static_cast<exprt>(if_exprt{
                          conjunction(guard), assignment.rhs, assignment.lhs}),
        ns)
      .get();

  // Note the following two calls are specifically required for
  // field-sensitivity. For example, with-expressions, which may have just been
  // introduced by symex_assign_struct_member, are transformed into member
  // expressions on the lhs. If we add an option to disable field-sensitivity
  // in the future these should be omitted.
  assignment = rewrite_with_to_field_symbols(
    state,
    shift_indexed_access_to_lhs(
      state, std::move(assignment), ns, symex_config.simplify_opt),
    ns);

  if(symex_config.simplify_opt)
    assignment.rhs = simplify_expr(std::move(assignment.rhs), ns);

  const ssa_exprt l2_lhs = state
                             .assignment(
                               assignment.lhs,
                               assignment.rhs,
                               ns,
                               symex_config.simplify_opt,
                               symex_config.constant_propagation,
                               symex_config.allow_pointer_unsoundness)
                             .get();

  state.record_events.push(false);
  const exprt l2_full_lhs =
    state.rename(assignment.original_lhs_skeleton.apply(l2_lhs), ns).get();
  state.record_events.pop();

  auto current_assignment_type =
    ns.lookup(l2_lhs.get_object_name()).is_auxiliary
      ? symex_targett::assignment_typet::HIDDEN
      : assignment_type;

  target.assignment(
    make_and(state.guard.as_expr(), conjunction(guard)),
    l2_lhs,
    l2_full_lhs,
    get_original_name(l2_full_lhs),
    assignment.rhs,
    state.source,
    current_assignment_type);

  const ssa_exprt &l1_lhs = assignment.lhs;
  if(field_sensitivityt::is_divisible(l1_lhs))
  {
    // Split composite symbol assignment.lhs into its components
    state.field_sensitivity.field_assignments(
      ns, state, l1_lhs, target, symex_config.allow_pointer_unsoundness);
    // Erase the composite symbol from our working state. Note that we need to
    // have it in the propagation table and the value set while doing the field
    // assignments, thus we cannot skip putting it in there above.
    state.propagation.erase_if_exists(l1_lhs.get_identifier());
    state.value_set.erase_symbol(l1_lhs, ns);
  }
}

void symex_assignt::assign_symbol(
  const assignmentt<ssa_exprt> &assignment, // L1
  const exprt::operandst &guard)
{
  // Shortcut the common case of a whole-struct initializer:
  if(assignment.rhs.id() == ID_struct)
    assign_from_struct(
      assignment.lhs,
      assignment.original_lhs_skeleton,
      to_struct_expr(assignment.rhs),
      guard);
  else
    assign_non_struct_symbol(assignment, guard);
}

void symex_assignt::assign_typecast(
  const assignmentt<typecast_exprt> &assignment,
  exprt::operandst &guard)
{
  assignmentt<exprt> new_assignment;
  // these may come from dereferencing on the assignment.lhs
  new_assignment.rhs = typecast_exprt::conditional_cast(
    assignment.rhs, assignment.lhs.op().type());
  new_assignment.original_lhs_skeleton =
    assignment.original_lhs_skeleton.compose(
      expr_skeletont::remove_op0(assignment.lhs));
  new_assignment.lhs = assignment.lhs.op();
  assign_rec(new_assignment, guard);
}

void symex_assignt::assign_array(
  const assignmentt<index_exprt> &assignment,
  exprt::operandst &guard)
{
  assignmentt<exprt> new_assignment;
  new_assignment.lhs = assignment.lhs.array();
  const exprt &lhs_index = assignment.lhs.index();
  const typet &lhs_index_type = new_assignment.lhs.type();

  PRECONDITION(lhs_index_type.id() == ID_array);

#ifdef USE_UPDATE

  // turn
  //   a[i]=e
  // into
  //   a'==UPDATE(a, [i], e)

  update_exprt new_rhs(assignment.lhs_index_type);
  new_rhs.old() = new_assignment.lhs;
  new_rhs.designator().push_back(index_designatort(lhs_index));
  new_rhs.new_value() = assignment.rhs;

  exprt new_full_lhs =
    add_to_lhs(assignment.original_lhs_skeleton, assignment.lhs);

  rec(new_assignment, guard);

#else
  // turn
  //   a[i]=e
  // into
  //   a'==a WITH [i:=e]

  new_assignment.rhs =
    with_exprt{new_assignment.lhs, lhs_index, assignment.rhs};
  new_assignment.original_lhs_skeleton =
    assignment.original_lhs_skeleton.compose(
      expr_skeletont::remove_op0(assignment.lhs));
  assign_rec(new_assignment, guard);
#endif
}

void symex_assignt::assign_struct_member(
  const assignmentt<member_exprt> &assignment,
  exprt::operandst &guard)
{
  // Symbolic execution of a struct member assignment.
  assignmentt<exprt> new_assignment;

  // lhs must be member operand, which
  // takes one operand, which must be a structure.

  new_assignment.lhs = assignment.lhs.op();

  // typecasts involved? C++ does that for inheritance.
  if(new_assignment.lhs.id() == ID_typecast)
  {
    if(to_typecast_expr(new_assignment.lhs).op().id() == ID_null_object)
    {
      // ignore, and give up
      return;
    }
    else
    {
      // remove the type cast, we assume that the member is there
      exprt tmp = to_typecast_expr(new_assignment.lhs).op();

      if(tmp.type().id() == ID_struct || tmp.type().id() == ID_struct_tag)
        new_assignment.lhs = tmp;
      else
        return; // ignore and give up
    }
  }

  const irep_idt &component_name = assignment.lhs.get_component_name();

#ifdef USE_UPDATE

  // turn
  //   a.c=e
  // into
  //   a'==UPDATE(a, .c, e)

  update_exprt new_rhs(assignment.lhs_struct.type());
  new_rhs.old() = assignment.lhs_struct;
  new_rhs.designator().push_back(member_designatort(component_name));
  new_rhs.new_value() = assignment.rhs;

  exprt new_full_lhs =
    add_to_lhs(assignment.original_lhs_skeleton, assignment.lhs);

  rec(new_assignment, guard);

#else
  // turn
  //   a.c=e
  // into
  //   a'==a WITH [c:=e]

  new_assignment.rhs = [&] {
    with_exprt tmp_rhs{
      new_assignment.lhs, exprt(ID_member_name), assignment.rhs};
    tmp_rhs.where().set(ID_component_name, component_name);
    return tmp_rhs;
  }();

  new_assignment.original_lhs_skeleton =
    assignment.original_lhs_skeleton.compose(
      expr_skeletont::remove_op0(assignment.lhs));
  assign_rec(new_assignment, guard);
#endif
}

void symex_assignt::assign_if(
  const assignmentt<if_exprt> &assignment,
  exprt::operandst &guard)
{
  // we have (c?a:b)=e;
  exprt renamed_guard = state.rename(assignment.lhs.cond(), ns).get();
  if(symex_config.simplify_opt)
    renamed_guard = simplify_expr(std::move(renamed_guard), ns);

  if(!renamed_guard.is_false())
  {
    guard.push_back(renamed_guard);
    assign_rec(replace_lhs(assignment, assignment.lhs.true_case()), guard);
    guard.pop_back();
  }

  if(!renamed_guard.is_true())
  {
    guard.push_back(not_exprt(renamed_guard));
    assign_rec(replace_lhs(assignment, assignment.lhs.false_case()), guard);
    guard.pop_back();
  }
}

void symex_assignt::assign_byte_extract(
  const assignmentt<byte_extract_exprt> &assignment,
  exprt::operandst &guard)
{
  // we have byte_extract_X(object, offset)=value
  // turn into object=byte_update_X(object, offset, value)
  assignmentt<exprt> new_assignment;
  irep_idt byte_update_id;
  if(assignment.lhs.id() == ID_byte_extract_little_endian)
    byte_update_id = ID_byte_update_little_endian;
  else if(assignment.lhs.id() == ID_byte_extract_big_endian)
    byte_update_id = ID_byte_update_big_endian;
  else
    UNREACHABLE;

  new_assignment.lhs = assignment.lhs.op();
  new_assignment.rhs = byte_update_exprt{byte_update_id,
                                         new_assignment.lhs,
                                         assignment.lhs.offset(),
                                         assignment.rhs};
  new_assignment.original_lhs_skeleton =
    assignment.original_lhs_skeleton.compose(
      expr_skeletont::remove_op0(assignment.lhs));
  assign_rec(new_assignment, guard);
}
