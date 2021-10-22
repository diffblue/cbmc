/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>

void goto_symext::havoc_rec(
  statet &state,
  const guardt &guard,
  const exprt &dest)
{
  if(dest.id()==ID_symbol)
  {
    exprt lhs;

    if(guard.is_true())
      lhs=dest;
    else
      lhs=if_exprt(
        guard.as_expr(), dest, exprt(ID_null_object, dest.type()));

    auto rhs =
      side_effect_expr_nondett(dest.type(), state.source.pc->source_location());

    symex_assign(state, lhs, rhs);
  }
  else if(dest.id()==ID_byte_extract_little_endian ||
          dest.id()==ID_byte_extract_big_endian)
  {
    havoc_rec(state, guard, to_byte_extract_expr(dest).op());
  }
  else if(dest.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(dest);

    guardt guard_t=state.guard;
    guard_t.add(if_expr.cond());
    havoc_rec(state, guard_t, if_expr.true_case());

    guardt guard_f=state.guard;
    guard_f.add(not_exprt(if_expr.cond()));
    havoc_rec(state, guard_f, if_expr.false_case());
  }
  else if(dest.id()==ID_typecast)
  {
    havoc_rec(state, guard, to_typecast_expr(dest).op());
  }
  else if(dest.id()==ID_index)
  {
    havoc_rec(state, guard, to_index_expr(dest).array());
  }
  else if(dest.id()==ID_member)
  {
    havoc_rec(state, guard, to_member_expr(dest).struct_op());
  }
  else
  {
    // consider printing a warning
  }
}

void goto_symext::symex_other(
  statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const codet &code = instruction.get_other();

  const irep_idt &statement=code.get_statement();

  if(statement==ID_expression)
  {
    // ignore
  }
  else if(statement==ID_cpp_delete ||
          statement=="cpp_delete[]")
  {
    const codet clean_code = to_code(clean_expr(code, state, false));
    symex_cpp_delete(state, clean_code);
  }
  else if(statement==ID_printf)
  {
    const codet clean_code = to_code(clean_expr(code, state, false));
    symex_printf(state, clean_code);
  }
  else if(can_cast_expr<code_inputt>(code))
  {
    const codet clean_code = to_code(clean_expr(code, state, false));
    symex_input(state, clean_code);
  }
  else if(can_cast_expr<code_outputt>(code))
  {
    const codet clean_code = to_code(clean_expr(code, state, false));
    symex_output(state, clean_code);
  }
  else if(statement==ID_decl)
  {
    UNREACHABLE; // see symex_decl.cpp
  }
  else if(statement==ID_nondet)
  {
    // like skip
  }
  else if(statement==ID_asm)
  {
    // we ignore this for now
  }
  else if(statement==ID_array_copy ||
          statement==ID_array_replace)
  {
    // array_copy and array_replace take two pointers (to arrays); we need to:
    // 1. remove any dereference expressions (via clean_expr)
    // 2. find the actual array objects/candidates for objects (via
    // process_array_expr)
    // 3. build an assignment where the type on lhs and rhs is:
    // - array_copy: the type of the first array (even if the second is smaller)
    // - array_replace: the type of the second array (even if it is smaller)
    DATA_INVARIANT(
      code.operands().size() == 2,
      "expected array_copy/array_replace statement to have two operands");

    // we need to add dereferencing for both operands
    exprt dest_array = clean_expr(code.op0(), state, false);
    exprt src_array = clean_expr(code.op1(), state, false);

    // obtain the actual arrays
    process_array_expr(state, dest_array);
    process_array_expr(state, src_array);

    // check for size (or type) mismatch and adjust
    if(dest_array.type() != src_array.type())
    {
      if(statement==ID_array_copy)
      {
        src_array = make_byte_extract(
          src_array, from_integer(0, index_type()), dest_array.type());
        do_simplify(src_array);
      }
      else
      {
        // ID_array_replace
        dest_array = make_byte_extract(
          dest_array, from_integer(0, index_type()), src_array.type());
        do_simplify(dest_array);
      }
    }

    symex_assign(state, dest_array, src_array);
  }
  else if(statement==ID_array_set)
  {
    // array_set takes a pointer (to an array) and a value that each element
    // should be set to; we need to:
    // 1. remove any dereference expressions (via clean_expr)
    // 2. find the actual array object/candidates for objects (via
    // process_array_expr)
    // 3. use the type of the resulting array to construct an array_of
    // expression
    DATA_INVARIANT(
      code.operands().size() == 2,
      "expected array_set statement to have two operands");

    // we need to add dereferencing for the first operand
    exprt array_expr = clean_expr(code.op0(), state, false);

    // obtain the actual array(s)
    process_array_expr(state, array_expr);

    // prepare to build the array_of
    exprt value = clean_expr(code.op1(), state, false);

    // we might have a memset-style update of a non-array type - convert to a
    // byte array
    if(array_expr.type().id() != ID_array)
    {
      auto array_size = size_of_expr(array_expr.type(), ns);
      CHECK_RETURN(array_size.has_value());
      do_simplify(array_size.value());
      array_expr = make_byte_extract(
        array_expr,
        from_integer(0, index_type()),
        array_typet(char_type(), array_size.value()));
    }

    const array_typet &array_type = to_array_type(array_expr.type());

    if(array_type.subtype() != value.type())
      value = typecast_exprt(value, array_type.subtype());

    symex_assign(state, array_expr, array_of_exprt(value, array_type));
  }
  else if(statement==ID_array_equal)
  {
    // array_equal takes two pointers (to arrays) and the symbol that the result
    // should get assigned to; we need to:
    // 1. remove any dereference expressions (via clean_expr)
    // 2. find the actual array objects/candidates for objects (via
    // process_array_expr)
    // 3. build an assignment where the lhs is the previous third argument, and
    // the right-hand side is an equality over the arrays, if their types match;
    // if the types don't match the result trivially is false
    DATA_INVARIANT(
      code.operands().size() == 3,
      "expected array_equal statement to have three operands");

    // we need to add dereferencing for the first two
    exprt array1 = clean_expr(code.op0(), state, false);
    exprt array2 = clean_expr(code.op1(), state, false);

    // obtain the actual arrays
    process_array_expr(state, array1);
    process_array_expr(state, array2);

    exprt rhs = equal_exprt(array1, array2);

    // check for size (or type) mismatch
    if(array1.type() != array2.type())
      rhs = false_exprt();

    symex_assign(state, code.op2(), rhs);
  }
  else if(statement==ID_user_specified_predicate ||
          statement==ID_user_specified_parameter_predicates ||
          statement==ID_user_specified_return_predicates)
  {
    // like skip
  }
  else if(statement==ID_fence)
  {
    target.memory_barrier(state.guard.as_expr(), state.source);
  }
  else if(statement==ID_havoc_object)
  {
    DATA_INVARIANT(
      code.operands().size() == 1,
      "expected havoc_object statement to have one operand");

    exprt object = clean_expr(code.op0(), state, false);

    process_array_expr(state, object);
    havoc_rec(state, guardt(true_exprt(), guard_manager), object);
  }
  else
    UNREACHABLE;
}
