/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/byte_operators.h>

#include <pointer-analysis/value_set_dereference.h>
#include <pointer-analysis/rewrite_index.h>
#include <langapi/language_util.h>

#include <ansi-c/c_types.h>

#include "goto_symex.h"
#include "renaming_ns.h"
#include "symex_dereference_state.h"

/*******************************************************************\

Function: goto_symext::dereference_rec_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: goto_symext::is_index_member_symbol_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: goto_symext::address_arithmetic

  Inputs:

 Outputs:

 Purpose: Evaluate an ID_address_of expression

\*******************************************************************/

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
        a.object()=index_exprt(a.object(), gen_zero(index_type()));
    }

    // do (expr.type() *)(((char *)op)+offset)
    result=typecast_exprt(result, pointer_typet(char_type()));

    // there could be further dereferencing in the offset
    exprt offset=be.offset();
    dereference_rec(offset, state, guard, false);

    result=plus_exprt(result, offset);

    // treat &array as &array[0]
    const typet &expr_type=ns.follow(expr.type());
    pointer_typet dest_type;

    if(expr_type.id()==ID_array && !keep_array)
      dest_type.subtype()=expr_type.subtype();
    else
      dest_type.subtype()=expr_type;

    result=typecast_exprt(result, dest_type);
  }
  else if(expr.id()==ID_index ||
          expr.id()==ID_member)
  {
    object_descriptor_exprt ode;
    ode.build(expr, ns);

    byte_extract_exprt be(byte_extract_id());
    be.type()=expr.type();
    be.op()=ode.root_object();
    be.offset()=ode.offset();

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
      result=index_exprt(result, gen_zero(index_type()));

    // TODO: consider pointer offset for ID_SSA_symbol
    result=address_of_exprt(result);
  }
  else
    throw "goto_symext::address_arithmetic does not handle "+expr.id_string();

  const typet &expr_type=ns.follow(expr.type());
  assert((expr_type.id()==ID_array && !keep_array) ||
         base_type_eq(pointer_typet(expr_type), result.type(), ns));

  return result;
}

/*******************************************************************\

Function: goto_symext::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::dereference_rec(
  exprt &expr,
  statet &state,
  guardt &guard,
  const bool write)
{
  if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw "dereference takes one operand";

    exprt tmp1;
    tmp1.swap(expr.op0());
    
    // first make sure there are no dereferences in there
    dereference_rec(tmp1, state, guard, false);

    // we need to set up some elaborate call-backs
    symex_dereference_statet symex_dereference_state(*this, state);
    renaming_nst renaming_ns(ns, state);

    value_set_dereferencet dereference(
      renaming_ns,
      new_symbol_table,
      options,
      symex_dereference_state);      
    
    // std::cout << "**** " << from_expr(ns, "", tmp1) << std::endl;
    exprt tmp2=dereference.dereference(
      tmp1, guard, write?value_set_dereferencet::WRITE:value_set_dereferencet::READ);
    //std::cout << "**** " << from_expr(ns, "", tmp2) << std::endl;

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
    address_of_expr.type()=pointer_typet(expr.type());

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
    assert(false);
  }
  else if(expr.id()==ID_address_of)
  {
    address_of_exprt &address_of_expr=to_address_of_expr(expr);
    
    exprt &object=address_of_expr.object();

    const typet &expr_type=ns.follow(expr.type());
    expr=address_arithmetic(object, state, guard,
                            expr_type.subtype().id()==ID_array);
  }
  else if(expr.id()==ID_typecast)
  {
    exprt &tc_op=to_typecast_expr(expr).op();

    // turn &array into &array[0] when casting to pointer-to-element-type
    if(tc_op.id()==ID_address_of &&
       to_address_of_expr(tc_op).object().type().id()==ID_array &&
       base_type_eq(
         expr.type(),
         pointer_typet(to_address_of_expr(tc_op).object().type().subtype()),
         ns))
    {
      expr=address_of_exprt(index_exprt(
          to_address_of_expr(tc_op).object(),
          gen_zero(index_type())));;

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

/*******************************************************************\

Function: goto_symext::dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::dereference(
  exprt &expr,
  statet &state,
  const bool write)
{
  // The expression needs to be renamed to level 1
  // in order to distinguish addresses of local variables
  // from different frames. Would be enough to rename
  // symbols whose address is taken.
  assert(!state.call_stack().empty());
  state.rename(expr, ns, goto_symex_statet::L1);

  // start the recursion!
  guardt guard;  
  dereference_rec(expr, state, guard, write);
}
