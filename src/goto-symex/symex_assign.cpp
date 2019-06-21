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

constexpr bool use_update()
{
#ifdef USE_UPDATE
  return true;
#else
  return false;
#endif
}

/// Store the \p what expression by recursively descending into the operands
/// of \p lhs until the first operand \c op0 is _nil_: this _nil_ operand
/// is then replaced with \p what.
/// \param lhs: Non-symbol pointed-to expression
/// \param what: The expression to be added to the \p lhs
/// \return The resulting expression
static exprt add_to_lhs(const exprt &lhs, const exprt &what)
{
  PRECONDITION(lhs.id() != ID_symbol);
  exprt tmp_what=what;

  if(tmp_what.id()!=ID_symbol)
  {
    PRECONDITION(tmp_what.operands().size() >= 1);
    tmp_what.op0().make_nil();
  }

  exprt new_lhs=lhs;

  exprt *p=&new_lhs;

  while(p->is_not_nil())
  {
    INVARIANT(
      p->id() != ID_symbol,
      "expected pointed-to expression not to be a symbol");
    INVARIANT(
      p->operands().size() >= 1,
      "expected pointed-to expression to have at least one operand");
    p=&p->op0();
  }

  INVARIANT(p->is_nil(), "expected pointed-to expression to be nil");

  *p=tmp_what;
  return new_lhs;
}

void symex_assignt::assign_rec(
  const exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  if(lhs.id() == ID_symbol && lhs.get_bool(ID_C_SSA_symbol))
  {
    assign_symbol(to_ssa_expr(lhs), full_lhs, rhs, guard);
  }
  else if(lhs.id() == ID_index)
    assign_array(to_index_expr(lhs), full_lhs, rhs, guard);
  else if(lhs.id()==ID_member)
  {
    const typet &type = to_member_expr(lhs).struct_op().type();
    if(type.id() == ID_struct || type.id() == ID_struct_tag)
      assign_struct_member(to_member_expr(lhs), full_lhs, rhs, guard);
    else if(type.id() == ID_union || type.id() == ID_union_tag)
    {
      // should have been replaced by byte_extract
      throw unsupported_operation_exceptiont(
        "assign_rec: unexpected assignment to union member");
    }
    else
      throw unsupported_operation_exceptiont(
        "assign_rec: unexpected assignment to member of `" + type.id_string() +
        "'");
  }
  else if(lhs.id()==ID_if)
    assign_if(to_if_expr(lhs), full_lhs, rhs, guard);
  else if(lhs.id()==ID_typecast)
    assign_typecast(to_typecast_expr(lhs), full_lhs, rhs, guard);
  else if(lhs.id() == ID_string_constant ||
          lhs.id() == ID_null_object ||
          lhs.id() == "zero_string" ||
          lhs.id() == "is_zero_string" ||
          lhs.id() == "zero_string_length")
  {
    // ignore
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    assign_byte_extract(to_byte_extract_expr(lhs), full_lhs, rhs, guard);
  }
  else if(lhs.id() == ID_complex_real)
  {
    // this is stuff like __real__ x = 1;
    const complex_real_exprt &complex_real_expr = to_complex_real_expr(lhs);

    const complex_imag_exprt complex_imag_expr(complex_real_expr.op());

    complex_exprt new_rhs(
      rhs, complex_imag_expr, to_complex_type(complex_real_expr.op().type()));

    assign_rec(complex_real_expr.op(), full_lhs, new_rhs, guard);
  }
  else if(lhs.id() == ID_complex_imag)
  {
    const complex_imag_exprt &complex_imag_expr = to_complex_imag_expr(lhs);

    const complex_real_exprt complex_real_expr(complex_imag_expr.op());

    complex_exprt new_rhs(
      complex_real_expr, rhs, to_complex_type(complex_imag_expr.op().type()));

    assign_rec(complex_imag_expr.op(), full_lhs, new_rhs, guard);
  }
  else
    throw unsupported_operation_exceptiont(
      "assignment to `" + lhs.id_string() + "' not handled");
}

/// Assignment from the rhs value to the lhs variable
struct assignmentt final
{
  ssa_exprt lhs;
  exprt rhs;
};

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
template <bool use_update>
static assignmentt rewrite_with_to_field_symbols(
  goto_symext::statet &state,
  assignmentt assignment,
  const namespacet &ns)
{
  exprt &ssa_rhs = assignment.rhs;
  ssa_exprt &lhs_mod = assignment.lhs;
  if(use_update)
  {
    while(ssa_rhs.id() == ID_update &&
          to_update_expr(ssa_rhs).designator().size() == 1 &&
          (lhs_mod.type().id() == ID_array ||
           lhs_mod.type().id() == ID_struct ||
           lhs_mod.type().id() == ID_struct_tag))
    {
      exprt field_sensitive_lhs;
      const update_exprt &update = to_update_expr(ssa_rhs);
      PRECONDITION(update.designator().size() == 1);
      const exprt &designator = update.designator().front();

      if(lhs_mod.type().id() == ID_array)
      {
        field_sensitive_lhs =
          index_exprt(lhs_mod, to_index_designator(designator).index());
      }
      else
      {
        field_sensitive_lhs = member_exprt(
          lhs_mod,
          to_member_designator(designator).get_component_name(),
          update.new_value().type());
      }

      state.field_sensitivity.apply(ns, state, field_sensitive_lhs, true);

      if(field_sensitive_lhs.id() != ID_symbol)
        break;

      ssa_rhs = update.new_value();
      lhs_mod = to_ssa_expr(field_sensitive_lhs);
    }
  }
  else
  {
    while(
      ssa_rhs.id() == ID_with && to_with_expr(ssa_rhs).operands().size() == 3 &&
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
  }
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
static assignmentt shift_indexed_access_to_lhs(
  goto_symext::statet &state,
  assignmentt assignment,
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
      return assignmentt{to_ssa_expr(byte_extract), byte_update.value()};
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
      return assignmentt{to_ssa_expr(byte_extract),
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
  const exprt &full_lhs,
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

    assign_symbol(to_ssa_expr(lhs_field), full_lhs, comp_rhs.second, guard);
  }
}

void symex_assignt::assign_non_struct_symbol(
  const ssa_exprt &lhs, // L1
  const exprt &full_lhs,
  const exprt &rhs,
  const exprt::operandst &guard)
{
  exprt l2_rhs =
    state
      .rename(
        // put assignment guard into the rhs
        guard.empty()
          ? rhs
          : static_cast<exprt>(if_exprt{conjunction(guard), rhs, lhs}),
        ns)
      .get();

  // Note the following two calls are specifically required for
  // field-sensitivity. For example, with-expressions, which may have just been
  // introduced by assign_struct_member, are transformed into member
  // expressions on the LHS. If we add an option to disable field-sensitivity
  // in the future these should be omitted.
  auto assignment = shift_indexed_access_to_lhs(
    state, assignmentt{lhs, std::move(l2_rhs)}, ns, symex_config.simplify_opt);
  assignment = rewrite_with_to_field_symbols<use_update()>(
    state, std::move(assignment), ns);

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
    state.rename(add_to_lhs(full_lhs, l2_lhs), ns).get();
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
    // Split composite symbol lhs into its components
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
  const ssa_exprt &lhs, // L1
  const exprt &full_lhs,
  const exprt &rhs,
  const exprt::operandst &guard)
{
  // Shortcut the common case of a whole-struct initializer:
  if(rhs.id() == ID_struct)
    assign_from_struct(lhs, full_lhs, to_struct_expr(rhs), guard);
  else
    assign_non_struct_symbol(lhs, full_lhs, rhs, guard);
}

void symex_assignt::assign_typecast(
  const typecast_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // these may come from dereferencing on the lhs
  exprt rhs_typecasted = typecast_exprt::conditional_cast(rhs, lhs.op().type());

  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);
  assign_rec(lhs.op(), new_full_lhs, rhs_typecasted, guard);
}

void symex_assignt::assign_array(
  const index_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  const exprt &lhs_array=lhs.array();
  const exprt &lhs_index=lhs.index();
  const typet &lhs_index_type = lhs_array.type();

  PRECONDITION(lhs_index_type.id() == ID_array);

#ifdef USE_UPDATE

  // turn
  //   a[i]=e
  // into
  //   a'==UPDATE(a, [i], e)

  update_exprt new_rhs(lhs_index_type);
  new_rhs.old()=lhs_array;
  new_rhs.designator().push_back(index_designatort(lhs_index));
  new_rhs.new_value()=rhs;

  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);

  symex_assign_rec(
    state, lhs_array, new_full_lhs, new_rhs, guard, assignment_type);

  #else
  // turn
  //   a[i]=e
  // into
  //   a'==a WITH [i:=e]

  const with_exprt new_rhs{lhs_array, lhs_index, rhs};
  const exprt new_full_lhs = add_to_lhs(full_lhs, lhs);

  assign_rec(lhs_array, new_full_lhs, new_rhs, guard);
#endif
}

void symex_assignt::assign_struct_member(
  const member_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // Symbolic execution of a struct member assignment.

  // lhs must be member operand, which
  // takes one operand, which must be a structure.

  exprt lhs_struct = lhs.op();

  // typecasts involved? C++ does that for inheritance.
  if(lhs_struct.id()==ID_typecast)
  {
    if(to_typecast_expr(lhs_struct).op().id() == ID_null_object)
    {
      // ignore, and give up
      return;
    }
    else
    {
      // remove the type cast, we assume that the member is there
      exprt tmp = to_typecast_expr(lhs_struct).op();

      if(tmp.type().id() == ID_struct || tmp.type().id() == ID_struct_tag)
        lhs_struct=tmp;
      else
        return; // ignore and give up
    }
  }

  const irep_idt &component_name=lhs.get_component_name();

  #ifdef USE_UPDATE

  // turn
  //   a.c=e
  // into
  //   a'==UPDATE(a, .c, e)

  update_exprt new_rhs(lhs_struct.type());
  new_rhs.old()=lhs_struct;
  new_rhs.designator().push_back(member_designatort(component_name));
  new_rhs.new_value()=rhs;

  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);

  symex_assign_rec(
    state, lhs_struct, new_full_lhs, new_rhs, guard, assignment_type);

  #else
  // turn
  //   a.c=e
  // into
  //   a'==a WITH [c:=e]

  with_exprt new_rhs(lhs_struct, exprt(ID_member_name), rhs);
  new_rhs.where().set(ID_component_name, component_name);

  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);
  assign_rec(lhs_struct, new_full_lhs, new_rhs, guard);
#endif
}

void symex_assignt::assign_if(
  const if_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // we have (c?a:b)=e;
  exprt renamed_guard = state.rename(lhs.cond(), ns).get();
  if(symex_config.simplify_opt)
    renamed_guard = simplify_expr(std::move(renamed_guard), ns);

  if(!renamed_guard.is_false())
  {
    guard.push_back(renamed_guard);
    assign_rec(lhs.true_case(), full_lhs, rhs, guard);
    guard.pop_back();
  }

  if(!renamed_guard.is_true())
  {
    guard.push_back(not_exprt(renamed_guard));
    assign_rec(lhs.false_case(), full_lhs, rhs, guard);
    guard.pop_back();
  }
}

void symex_assignt::assign_byte_extract(
  const byte_extract_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // we have byte_extract_X(object, offset)=value
  // turn into object=byte_update_X(object, offset, value)

  irep_idt byte_update_id;
  if(lhs.id()==ID_byte_extract_little_endian)
    byte_update_id = ID_byte_update_little_endian;
  else if(lhs.id()==ID_byte_extract_big_endian)
    byte_update_id = ID_byte_update_big_endian;
  else
    UNREACHABLE;

  const byte_update_exprt new_rhs{byte_update_id, lhs.op(), lhs.offset(), rhs};
  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);
  assign_rec(lhs.op(), new_full_lhs, new_rhs, guard);
}
