/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/expr_iterator.h>
#include <util/nodiscard.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

#include "expr_skeleton.h"
#include "path_storage.h"
#include "symex_assign.h"
#include "symex_dereference_state.h"

#include <pointer-analysis/value_set_dereference.h>

/// Given an expression, find the root object and the offset into it.
///
/// The extra complication to be considered here is that the expression may
/// have any number of ternary expressions mixed with type casts.
static void
process_array_expr(exprt &expr, bool do_simplify, const namespacet &ns)
{
  // This may change the type of the expression!

  if(expr.id()==ID_if)
  {
    if_exprt &if_expr=to_if_expr(expr);
    process_array_expr(if_expr.true_case(), do_simplify, ns);
    process_array_expr(if_expr.false_case(), do_simplify, ns);

    if(if_expr.true_case() != if_expr.false_case())
    {
      byte_extract_exprt be = make_byte_extract(
        if_expr.false_case(),
        from_integer(0, c_index_type()),
        if_expr.true_case().type());

      if_expr.false_case().swap(be);
    }

    if_expr.type()=if_expr.true_case().type();
  }
  else if(expr.id()==ID_address_of)
  {
    // strip
    exprt tmp = to_address_of_expr(expr).object();
    expr.swap(tmp);
    process_array_expr(expr, do_simplify, ns);
  }
  else if(
    is_ssa_expr(expr) && to_ssa_expr(expr).get_original_expr().id() == ID_index)
  {
    const ssa_exprt &ssa=to_ssa_expr(expr);
    const index_exprt &index_expr=to_index_expr(ssa.get_original_expr());
    exprt tmp=index_expr.array();
    expr.swap(tmp);

    process_array_expr(expr, do_simplify, ns);
  }
  else if(expr.id() != ID_symbol)
  {
    object_descriptor_exprt ode;
    ode.build(expr, ns);

    expr = ode.root_object();

    // If we arrive at a void-typed object (typically the result of failing to
    // dereference a void* pointer) there is nothing else to be done - it has
    // void-type and the caller needs to handle this case gracefully.
    if(expr.type().id() == ID_empty)
      return;

    if(!ode.offset().is_zero())
    {
      if(expr.type().id() != ID_array)
      {
        auto array_size = size_of_expr(expr.type(), ns);
        CHECK_RETURN(array_size.has_value());
        if(do_simplify)
          simplify(array_size.value(), ns);
        expr = make_byte_extract(
          expr,
          from_integer(0, c_index_type()),
          array_typet(char_type(), array_size.value()));
      }

      // given an array type T[N], i.e., an array of N elements of type T, and a
      // byte offset B, compute the array offset B/sizeof(T) and build a new
      // type T[N-(B/sizeof(T))]
      const array_typet &prev_array_type = to_array_type(expr.type());
      const typet &array_size_type = prev_array_type.size().type();
      const typet &subtype = prev_array_type.element_type();

      exprt new_offset =
        typecast_exprt::conditional_cast(ode.offset(), array_size_type);
      auto subtype_size_opt = size_of_expr(subtype, ns);
      CHECK_RETURN(subtype_size_opt.has_value());
      exprt subtype_size = typecast_exprt::conditional_cast(
        subtype_size_opt.value(), array_size_type);
      new_offset = div_exprt(new_offset, subtype_size);
      minus_exprt subtraction{prev_array_type.size(), new_offset};
      if_exprt new_size{
        binary_predicate_exprt{
          subtraction, ID_ge, from_integer(0, subtraction.type())},
        subtraction,
        from_integer(0, subtraction.type())};
      if(do_simplify)
        simplify(new_size, ns);

      array_typet new_array_type(subtype, new_size);

      expr = make_byte_extract(expr, ode.offset(), new_array_type);
    }
  }
}

void goto_symext::process_array_expr(statet &state, exprt &expr)
{
  symex_dereference_statet symex_dereference_state(state, ns);

  value_set_dereferencet dereference(
    ns, state.symbol_table, symex_dereference_state, language_mode, false, log);

  expr = dereference.dereference(expr, symex_config.show_points_to_sets);
  lift_lets(state, expr);

  ::process_array_expr(expr, symex_config.simplify_opt, ns);
}

/// Rewrite index/member expressions in byte_extract to offset
static void adjust_byte_extract_rec(exprt &expr, const namespacet &ns)
{
  Forall_operands(it, expr)
    adjust_byte_extract_rec(*it, ns);

  if(expr.id()==ID_byte_extract_big_endian ||
     expr.id()==ID_byte_extract_little_endian)
  {
    byte_extract_exprt &be=to_byte_extract_expr(expr);
    if(be.op().id()==ID_symbol &&
       to_ssa_expr(be.op()).get_original_expr().get_bool(ID_C_invalid_object))
      return;

    object_descriptor_exprt ode;
    ode.build(expr, ns);

    be.op()=ode.root_object();
    be.offset()=ode.offset();
  }
}

static void
replace_nondet(exprt &expr, symex_nondet_generatort &build_symex_nondet)
{
  if(expr.id() == ID_side_effect && expr.get(ID_statement) == ID_nondet)
  {
    expr = build_symex_nondet(expr.type(), expr.source_location());
  }
  else
  {
    Forall_operands(it, expr)
      replace_nondet(*it, build_symex_nondet);
  }
}

void goto_symext::lift_let(statet &state, const let_exprt &let_expr)
{
  exprt let_value = clean_expr(let_expr.value(), state, false);
  let_value = state.rename(std::move(let_value), ns).get();
  do_simplify(let_value);

  exprt::operandst value_assignment_guard;
  symex_assignt{
    state, symex_targett::assignment_typet::HIDDEN, ns, symex_config, target}
    .assign_symbol(
      to_ssa_expr(state.rename<L1>(let_expr.symbol(), ns).get()),
      expr_skeletont{},
      let_value,
      value_assignment_guard);

  // Schedule the bound variable to be cleaned up at the end of symex_step:
  instruction_local_symbols.push_back(let_expr.symbol());
}

void goto_symext::lift_lets(statet &state, exprt &rhs)
{
  for(auto it = rhs.depth_begin(), itend = rhs.depth_end(); it != itend;)
  {
    if(it->id() == ID_let)
    {
      // Visit post-order, so more-local definitions are made before usage:
      exprt &replaced_expr = it.mutate();
      let_exprt &replaced_let = to_let_expr(replaced_expr);
      lift_lets(state, replaced_let.value());
      lift_lets(state, replaced_let.where());

      lift_let(state, replaced_let);
      replaced_expr = replaced_let.where();

      it.next_sibling_or_parent();
    }
    else if(it->id() == ID_exists || it->id() == ID_forall)
    {
      // expressions within exists/forall may depend on bound variables, we
      // cannot safely lift let expressions out of those, just skip
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }
}

NODISCARD exprt
goto_symext::clean_expr(exprt expr, statet &state, const bool write)
{
  replace_nondet(expr, path_storage.build_symex_nondet);
  dereference(expr, state, write);
  lift_lets(state, expr);

  // make sure all remaining byte extract operations use the root
  // object to avoid nesting of with/update and byte_update when on
  // lhs
  if(write)
    adjust_byte_extract_rec(expr, ns);
  return expr;
}
