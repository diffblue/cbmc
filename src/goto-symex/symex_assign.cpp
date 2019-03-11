/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/exception_utils.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

#include "goto_symex_state.h"

// We can either use with_exprt or update_exprt when building expressions that
// modify components of an array or a struct. Set USE_UPDATE to use
// update_exprt.
// #define USE_UPDATE

void goto_symext::symex_assign(statet &state, const code_assignt &code)
{
  exprt lhs=code.lhs();
  exprt rhs=code.rhs();

  DATA_INVARIANT(
    lhs.type() == rhs.type(), "assignments must be type consistent");

  clean_expr(lhs, state, true);
  clean_expr(rhs, state, false);

  if(rhs.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(
      statement == ID_cpp_new || statement == ID_cpp_new_array ||
      statement == ID_java_new_array_data)
      symex_cpp_new(state, lhs, side_effect_expr);
    else if(statement==ID_allocate)
      symex_allocate(state, lhs, side_effect_expr);
    else if(statement==ID_printf)
    {
      PRECONDITION(lhs.is_nil());
      symex_printf(state, side_effect_expr);
    }
    else if(statement==ID_gcc_builtin_va_arg_next)
      symex_gcc_builtin_va_arg_next(state, lhs, side_effect_expr);
    else
      UNREACHABLE;
  }
  else
  {
    assignment_typet assignment_type=symex_targett::assignment_typet::STATE;

    // Let's hide return value assignments.
    if(lhs.id()==ID_symbol &&
       id2string(to_symbol_expr(lhs).get_identifier()).find(
                  "#return_value!")!=std::string::npos)
      assignment_type=symex_targett::assignment_typet::HIDDEN;

    // We hide if we are in a hidden function.
    if(state.call_stack().top().hidden_function)
      assignment_type=symex_targett::assignment_typet::HIDDEN;

    // We hide if we are executing a hidden instruction.
    if(state.source.pc->source_location.get_hide())
      assignment_type=symex_targett::assignment_typet::HIDDEN;

    exprt::operandst lhs_if_then_else_conditions;
    symex_assign_rec(
      state,
      lhs,
      nil_exprt(),
      rhs,
      lhs_if_then_else_conditions,
      assignment_type);
  }
}

exprt goto_symext::add_to_lhs(
  const exprt &lhs,
  const exprt &what)
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

void goto_symext::symex_assign_rec(
  statet &state,
  const exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  assignment_typet assignment_type)
{
  if(lhs.id()==ID_symbol &&
     lhs.get_bool(ID_C_SSA_symbol))
    symex_assign_symbol(
      state, to_ssa_expr(lhs), full_lhs, rhs, guard, assignment_type);
  else if(lhs.id()==ID_index)
    symex_assign_array(
      state, to_index_expr(lhs), full_lhs, rhs, guard, assignment_type);
  else if(lhs.id()==ID_member)
  {
    const typet &type = to_member_expr(lhs).struct_op().type();
    if(type.id() == ID_struct || type.id() == ID_struct_tag)
      symex_assign_struct_member(
        state, to_member_expr(lhs), full_lhs, rhs, guard, assignment_type);
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
  else if(lhs.id()==ID_if)
    symex_assign_if(
      state, to_if_expr(lhs), full_lhs, rhs, guard, assignment_type);
  else if(lhs.id()==ID_typecast)
    symex_assign_typecast(
      state, to_typecast_expr(lhs), full_lhs, rhs, guard, assignment_type);
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
    symex_assign_byte_extract(
      state, to_byte_extract_expr(lhs), full_lhs, rhs, guard, assignment_type);
  }
  else if(lhs.id() == ID_complex_real)
  {
    // this is stuff like __real__ x = 1;
    const complex_real_exprt &complex_real_expr = to_complex_real_expr(lhs);

    const complex_imag_exprt complex_imag_expr(complex_real_expr.op());

    complex_exprt new_rhs(
      rhs, complex_imag_expr, to_complex_type(complex_real_expr.op().type()));

    symex_assign_rec(
      state, complex_real_expr.op(), full_lhs, new_rhs, guard, assignment_type);
  }
  else if(lhs.id() == ID_complex_imag)
  {
    const complex_imag_exprt &complex_imag_expr = to_complex_imag_expr(lhs);

    const complex_real_exprt complex_real_expr(complex_imag_expr.op());

    complex_exprt new_rhs(
      complex_real_expr, rhs, to_complex_type(complex_imag_expr.op().type()));

    symex_assign_rec(
      state, complex_imag_expr.op(), full_lhs, new_rhs, guard, assignment_type);
  }
  else
    throw unsupported_operation_exceptiont(
      "assignment to `" + lhs.id_string() + "' not handled");
}

/// Replace "with" (or "update") expressions in \p ssa_rhs by their update
/// values and move the index or member to the left-hand side \p lhs_mod. This
/// effectively undoes the work that \ref goto_symext::symex_assign_array and
/// \ref goto_symext::symex_assign_struct_member have done, but now making use
/// of the index/member that may only be known after renaming to L2 has taken
/// place.
/// \param [in, out] state: symbolic execution state to perform renaming
/// \param [in,out] ssa_rhs: right-hand side
/// \param [in,out] lhs_mod: left-hand side
/// \param ns: namespace
static void rewrite_with_to_field_symbols(
  goto_symext::statet &state,
  exprt &ssa_rhs,
  ssa_exprt &lhs_mod,
  const namespacet &ns)
{
#ifdef USE_UPDATE
  while(ssa_rhs.id() == ID_update &&
        to_update_expr(ssa_rhs).designator().size() == 1 &&
        (lhs_mod.type().id() == ID_array || lhs_mod.type().id() == ID_struct ||
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

    state.field_sensitivity.apply(ns, state, field_sensitive_lhs, true);

    if(field_sensitive_lhs.id() != ID_symbol)
      break;

    ssa_rhs = with_expr.new_value();
    lhs_mod = to_ssa_expr(field_sensitive_lhs);
  }
#endif
}

/// Replace byte-update operations that only affect individual fields of an
/// expression by assignments to just those fields. May generate "with" (or
/// "update") expressions, which \ref rewrite_with_to_field_symbols will then
/// take care of.
/// \param [in,out] ssa_rhs: right-hand side
/// \param [in,out] lhs_mod: left-hand side
/// \param ns: namespace
/// \param do_simplify: set to true if, and only if, simplification is enabled
static void shift_indexed_access_to_lhs(
  goto_symext::statet &state,
  exprt &ssa_rhs,
  ssa_exprt &lhs_mod,
  const namespacet &ns,
  bool do_simplify)
{
  if(
    ssa_rhs.id() == ID_byte_update_little_endian ||
    ssa_rhs.id() == ID_byte_update_big_endian)
  {
    byte_update_exprt &byte_update = to_byte_update_expr(ssa_rhs);
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
      ssa_rhs = byte_update.value();
      lhs_mod = to_ssa_expr(byte_extract);
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

      lhs_mod = to_ssa_expr(byte_extract);
    }
  }

  rewrite_with_to_field_symbols(state, ssa_rhs, lhs_mod, ns);
}

void goto_symext::symex_assign_symbol(
  statet &state,
  const ssa_exprt &lhs, // L1
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  assignment_typet assignment_type)
{
  exprt ssa_rhs=rhs;

  // put assignment guard into the rhs
  if(!guard.empty())
  {
    if_exprt tmp_ssa_rhs(conjunction(guard), ssa_rhs, lhs, ssa_rhs.type());
    tmp_ssa_rhs.swap(ssa_rhs);
  }

  exprt l2_rhs = state.rename(std::move(ssa_rhs), ns).get();

  ssa_exprt lhs_mod = lhs;

  shift_indexed_access_to_lhs(
    state, l2_rhs, lhs_mod, ns, symex_config.simplify_opt);

  do_simplify(l2_rhs);

  ssa_exprt ssa_lhs = lhs_mod;
  state.assignment(
    ssa_lhs,
    l2_rhs,
    ns,
    symex_config.simplify_opt,
    symex_config.constant_propagation,
    symex_config.allow_pointer_unsoundness);

  exprt ssa_full_lhs=full_lhs;
  ssa_full_lhs=add_to_lhs(ssa_full_lhs, ssa_lhs);
  const bool record_events=state.record_events;
  state.record_events=false;
  exprt l2_full_lhs = state.rename(std::move(ssa_full_lhs), ns).get();
  state.record_events=record_events;

  // do the assignment
  const symbolt &symbol = ns.lookup(ssa_lhs.get_object_name());

  if(symbol.is_auxiliary)
    assignment_type=symex_targett::assignment_typet::HIDDEN;

  log.conditional_output(
    log.debug(),
    [this, &ssa_lhs](messaget::mstreamt &mstream) {
      mstream << "Assignment to " << ssa_lhs.get_identifier()
              << " ["
              << pointer_offset_bits(ssa_lhs.type(), ns).value_or(0)
              << " bits]"
              << messaget::eom;
    });

  // Temporarily add the state guard
  guard.emplace_back(state.guard.as_expr());

  exprt original_lhs = l2_full_lhs;
  get_original_name(original_lhs);
  target.assignment(
    conjunction(guard),
    ssa_lhs,
    l2_full_lhs,
    original_lhs,
    l2_rhs,
    state.source,
    assignment_type);

  state.field_sensitivity.field_assignments(ns, state, lhs_mod, target);

  // Restore the guard
  guard.pop_back();
}

void goto_symext::symex_assign_typecast(
  statet &state,
  const typecast_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  assignment_typet assignment_type)
{
  // these may come from dereferencing on the lhs
  exprt rhs_typecasted = typecast_exprt::conditional_cast(rhs, lhs.op().type());

  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);

  symex_assign_rec(
    state, lhs.op(), new_full_lhs, rhs_typecasted, guard, assignment_type);
}

void goto_symext::symex_assign_array(
  statet &state,
  const index_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  assignment_typet assignment_type)
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

  with_exprt new_rhs(lhs_array, lhs_index, rhs);
  new_rhs.type() = lhs_index_type;

  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);

  symex_assign_rec(
    state, lhs_array, new_full_lhs, new_rhs, guard, assignment_type);
  #endif
}

void goto_symext::symex_assign_struct_member(
  statet &state,
  const member_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  assignment_typet assignment_type)
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

  symex_assign_rec(
    state, lhs_struct, new_full_lhs, new_rhs, guard, assignment_type);
  #endif
}

void goto_symext::symex_assign_if(
  statet &state,
  const if_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  assignment_typet assignment_type)
{
  // we have (c?a:b)=e;
  exprt renamed_guard = state.rename(lhs.cond(), ns).get();
  do_simplify(renamed_guard);

  if(!renamed_guard.is_false())
  {
    guard.push_back(renamed_guard);
    symex_assign_rec(
      state, lhs.true_case(), full_lhs, rhs, guard, assignment_type);
    guard.pop_back();
  }

  if(!renamed_guard.is_true())
  {
    guard.push_back(not_exprt(renamed_guard));
    symex_assign_rec(
      state, lhs.false_case(), full_lhs, rhs, guard, assignment_type);
    guard.pop_back();
  }
}

void goto_symext::symex_assign_byte_extract(
  statet &state,
  const byte_extract_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  assignment_typet assignment_type)
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

  symex_assign_rec(
    state, lhs.op(), new_full_lhs, new_rhs, guard, assignment_type);
}
