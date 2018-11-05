/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>

#include <pointer-analysis/value_set_dereference.h>

#include "symex_dereference_state.h"

void goto_symext::dereference_rec_address_of(
  exprt &expr,
  statet &state,
  guardt &guard)
{
  // Could be member, could be if, could be index.

  if(expr.id()==ID_member)
    dereference_rec_address_of(
      to_member_expr(expr).struct_op(), state, guard);
  else if(expr.id()==ID_if)
  {
    // the condition is not an address
    dereference_rec(
      to_if_expr(expr).cond(), state, guard, false);

    // add to guard?
    dereference_rec_address_of(
      to_if_expr(expr).true_case(), state, guard);
    dereference_rec_address_of(
      to_if_expr(expr).false_case(), state, guard);
  }
  else if(expr.id()==ID_index)
  {
    // the index is not an address
    dereference_rec(
      to_index_expr(expr).index(), state, guard, false);

    // the array _is_ an address
    dereference_rec_address_of(
      to_index_expr(expr).array(), state, guard);
  }
  else
  {
    // give up and dereference

    dereference_rec(expr, state, guard, false);
  }
}

bool goto_symext::is_index_member_symbol_if(const exprt &expr)
{
  // Could be member, could be if, could be index.

  if(expr.id()==ID_member)
  {
    return is_index_member_symbol_if(
      to_member_expr(expr).struct_op());
  }
  else if(expr.id()==ID_if)
  {
    return
      is_index_member_symbol_if(to_if_expr(expr).true_case()) &&
      is_index_member_symbol_if(to_if_expr(expr).false_case());
  }
  else if(expr.id()==ID_index)
  {
    return is_index_member_symbol_if(to_index_expr(expr).array());
  }
  else if(expr.id()==ID_symbol)
    return true;
  else
    return false;
}

/// Evaluate an ID_address_of expression
exprt goto_symext::address_arithmetic(
  const exprt &expr,
  statet &state,
  guardt &guard,
  bool keep_array)
{
  exprt result;

  if(expr.id()==ID_byte_extract_little_endian ||
     expr.id()==ID_byte_extract_big_endian)
  {
    // address_of(byte_extract(op, offset, t)) is
    // address_of(op) + offset with adjustments for arrays

    const byte_extract_exprt &be=to_byte_extract_expr(expr);

    // recursive call
    result=address_arithmetic(be.op(), state, guard, keep_array);

    if(ns.follow(be.op().type()).id()==ID_array &&
       result.id()==ID_address_of)
    {
      address_of_exprt &a=to_address_of_expr(result);

      // turn &a of type T[i][j] into &(a[0][0])
      for(const typet *t=&(ns.follow(a.type().subtype()));
          t->id()==ID_array && !base_type_eq(expr.type(), *t, ns);
          t=&(ns.follow(*t).subtype()))
        a.object()=index_exprt(a.object(), from_integer(0, index_type()));
    }

    // do (expr.type() *)(((char *)op)+offset)
    result=typecast_exprt(result, pointer_type(char_type()));

    // there could be further dereferencing in the offset
    exprt offset=be.offset();
    dereference_rec(offset, state, guard, false);

    result=plus_exprt(result, offset);

    // treat &array as &array[0]
    const typet &expr_type=ns.follow(expr.type());
    typet dest_type_subtype;

    if(expr_type.id()==ID_array && !keep_array)
      dest_type_subtype=expr_type.subtype();
    else
      dest_type_subtype=expr_type;

    result=typecast_exprt(result, pointer_type(dest_type_subtype));
  }
  else if(expr.id()==ID_index ||
          expr.id()==ID_member)
  {
    object_descriptor_exprt ode;
    ode.build(expr, ns);

    const byte_extract_exprt be(
      byte_extract_id(), ode.root_object(), ode.offset(), expr.type());

    // recursive call
    result=address_arithmetic(be, state, guard, keep_array);

    do_simplify(result);
  }
  else if(expr.id()==ID_dereference)
  {
    // ANSI-C guarantees &*p == p no matter what p is,
    // even if it's complete garbage
    // just grab the pointer, but be wary of further dereferencing
    // in the pointer itself
    result=to_dereference_expr(expr).pointer();
    dereference_rec(result, state, guard, false);
  }
  else if(expr.id()==ID_if)
  {
    if_exprt if_expr=to_if_expr(expr);

    // the condition is not an address
    dereference_rec(if_expr.cond(), state, guard, false);

    // recursive call
    if_expr.true_case()=
      address_arithmetic(if_expr.true_case(), state, guard, keep_array);
    if_expr.false_case()=
      address_arithmetic(if_expr.false_case(), state, guard, keep_array);

    result=if_expr;
  }
  else if(expr.id()==ID_symbol ||
          expr.id()==ID_string_constant ||
          expr.id()==ID_label ||
          expr.id()==ID_array)
  {
    // give up, just dereference
    result=expr;
    dereference_rec(result, state, guard, false);

    // turn &array into &array[0]
    if(ns.follow(result.type()).id()==ID_array && !keep_array)
      result=index_exprt(result, from_integer(0, index_type()));

    // handle field-sensitive SSA symbol
    mp_integer offset=0;
    if(expr.id()==ID_symbol &&
       expr.get_bool(ID_C_SSA_symbol))
    {
      auto offset_opt = compute_pointer_offset(expr, ns);
      PRECONDITION(offset_opt.has_value());
      offset = *offset_opt;
    }

    if(offset>0)
    {
      const byte_extract_exprt be(
        byte_extract_id(),
        to_ssa_expr(expr).get_l1_object(),
        from_integer(offset, index_type()),
        expr.type());

      result=address_arithmetic(be, state, guard, keep_array);

      do_simplify(result);
    }
    else
      result=address_of_exprt(result);
  }
  else if(expr.id() == ID_typecast)
  {
    const typecast_exprt &tc_expr = to_typecast_expr(expr);

    result = address_arithmetic(tc_expr.op(), state, guard, keep_array);

    // treat &array as &array[0]
    const typet &expr_type = ns.follow(expr.type());
    typet dest_type_subtype;

    if(expr_type.id() == ID_array && !keep_array)
      dest_type_subtype = expr_type.subtype();
    else
      dest_type_subtype = expr_type;

    result = typecast_exprt(result, pointer_type(dest_type_subtype));
  }
  else
    throw unsupported_operation_exceptiont(
      "goto_symext::address_arithmetic does not handle " + expr.id_string());

  const typet &expr_type=ns.follow(expr.type());
  INVARIANT((expr_type.id()==ID_array && !keep_array) ||
            base_type_eq(pointer_type(expr_type), result.type(), ns),
            "either non-persistent array or pointer to result");

  return result;
}

void goto_symext::dereference_rec(
  exprt &expr,
  statet &state,
  guardt &guard,
  const bool write)
{
  if(expr.id()==ID_dereference)
  {
    dereference_exprt to_check = to_dereference_expr(expr);
    bool expr_is_not_null = false;

    if(state.threads.size() == 1)
    {
      const irep_idt &expr_function = state.source.pc->function;
      if(!expr_function.empty())
      {
        state.get_original_name(to_check);

        expr_is_not_null =
          state.safe_pointers.at(expr_function).is_safe_dereference(
            to_check, state.source.pc);
      }
    }

    exprt tmp1;
    tmp1.swap(to_dereference_expr(expr).pointer());

    // first make sure there are no dereferences in there
    dereference_rec(tmp1, state, guard, false);

    // we need to set up some elaborate call-backs
    symex_dereference_statet symex_dereference_state(*this, state);

    value_set_dereferencet dereference(
      ns,
      state.symbol_table,
      symex_dereference_state,
      language_mode,
      expr_is_not_null);

    // std::cout << "**** " << format(tmp1) << '\n';
    exprt tmp2=
      dereference.dereference(
        tmp1,
        guard,
        write?
          value_set_dereferencet::modet::WRITE:
          value_set_dereferencet::modet::READ);
    // std::cout << "**** " << format(tmp2) << '\n';

    expr.swap(tmp2);

    // this may yield a new auto-object
    trigger_auto_object(expr, state);
  }
  else if(expr.id()==ID_index &&
          to_index_expr(expr).array().id()==ID_member &&
          to_array_type(ns.follow(to_index_expr(expr).array().type())).
            size().is_zero())
  {
    // This is an expression of the form x.a[i],
    // where a is a zero-sized array. This gets
    // re-written into *(&x.a+i)

    index_exprt index_expr=to_index_expr(expr);

    address_of_exprt address_of_expr(index_expr.array());
    address_of_expr.type()=pointer_type(expr.type());

    dereference_exprt tmp;
    tmp.pointer()=plus_exprt(address_of_expr, index_expr.index());
    tmp.type()=expr.type();
    tmp.add_source_location()=expr.source_location();

    // recursive call
    dereference_rec(tmp, state, guard, write);

    expr.swap(tmp);
  }
  else if(expr.id()==ID_index &&
          to_index_expr(expr).array().type().id()==ID_pointer)
  {
    // old stuff, will go away
    UNREACHABLE;
  }
  else if(expr.id()==ID_address_of)
  {
    address_of_exprt &address_of_expr=to_address_of_expr(expr);

    exprt &object=address_of_expr.object();

    const typet &expr_type=ns.follow(expr.type());
    expr = address_arithmetic(
      object,
      state,
      guard,
      to_pointer_type(expr_type).subtype().id() == ID_array);
  }
  else if(expr.id()==ID_typecast)
  {
    exprt &tc_op=to_typecast_expr(expr).op();

    // turn &array into &array[0] when casting to pointer-to-element-type
    if(tc_op.id()==ID_address_of &&
       to_address_of_expr(tc_op).object().type().id()==ID_array &&
       base_type_eq(
         expr.type(),
         pointer_type(to_address_of_expr(tc_op).object().type().subtype()),
         ns))
    {
      expr=
        address_of_exprt(
          index_exprt(
            to_address_of_expr(tc_op).object(),
            from_integer(0, index_type())));

      dereference_rec(expr, state, guard, write);
    }
    else
    {
      dereference_rec(tc_op, state, guard, write);
    }
  }
  else
  {
    Forall_operands(it, expr)
      dereference_rec(*it, state, guard, write);
  }
}

void goto_symext::dereference(
  exprt &expr,
  statet &state,
  const bool write)
{
  // The expression needs to be renamed to level 1
  // in order to distinguish addresses of local variables
  // from different frames. Would be enough to rename
  // symbols whose address is taken.
  PRECONDITION(!state.call_stack().empty());
  state.rename(expr, ns, goto_symex_statet::L1);

  // start the recursion!
  guardt guard;
  dereference_rec(expr, state, guard, write);
  // dereferencing may introduce new symbol_exprt
  // (like __CPROVER_memory)
  state.rename(expr, ns, goto_symex_statet::L1);
}
