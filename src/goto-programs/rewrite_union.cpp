/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "rewrite_union.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>

#include <goto-programs/goto_model.h>

static bool have_to_rewrite_union(const exprt &expr)
{
  if(expr.id() == ID_member)
  {
    const exprt &op = to_member_expr(expr).struct_op();

    if(op.type().id() == ID_union_tag || op.type().id() == ID_union)
      return true;
  }
  else if(expr.id() == ID_union)
    return true;

  for(const auto &op : expr.operands())
  {
    if(have_to_rewrite_union(op))
      return true;
  }

  return false;
}

// inside an address of (&x), unions can simply
// be type casts and don't have to be re-written!
static void rewrite_union(exprt &expr, const namespacet &ns);

static void rewrite_union_address_of(exprt &expr, const namespacet &ns)
{
  if(!have_to_rewrite_union(expr))
    return;

  if(expr.id() == ID_index)
  {
    rewrite_union_address_of(to_index_expr(expr).array(), ns);
    rewrite_union(to_index_expr(expr).index(), ns);
  }
  else if(expr.id() == ID_member)
    rewrite_union_address_of(to_member_expr(expr).struct_op(), ns);
  else if(expr.id() == ID_symbol)
  {
    // done!
  }
  else if(expr.id() == ID_dereference)
    rewrite_union(to_dereference_expr(expr).pointer(), ns);
}

/// We rewrite u.c for unions u into byte_extract(u, 0), and { .c = v } into
/// byte_update(NIL, 0, v)
static void rewrite_union(exprt &expr, const namespacet &ns)
{
  if(expr.id() == ID_address_of)
  {
    rewrite_union_address_of(to_address_of_expr(expr).object(), ns);
    return;
  }

  if(!have_to_rewrite_union(expr))
    return;

  Forall_operands(it, expr)
    rewrite_union(*it, ns);

  if(expr.id() == ID_member)
  {
    const exprt &op = to_member_expr(expr).struct_op();

    if(op.type().id() == ID_union_tag || op.type().id() == ID_union)
    {
      if(
        expr.type().id() != ID_c_bit_field ||
        to_c_bit_field_type(expr.type()).get_width() %
            config.ansi_c.char_width ==
          0)
      {
        exprt offset = from_integer(0, c_index_type());
        expr = make_byte_extract(op, offset, expr.type());
      }
      else
      {
        const auto &bf_type = to_c_bit_field_type(expr.type());
        std::size_t bf_width = bf_type.get_width();

        auto union_width = pointer_offset_bits(op.type(), ns);
        CHECK_RETURN(union_width.has_value() && *union_width > 0);
        std::size_t W = numeric_cast_v<std::size_t>(*union_width);

        std::size_t bit_offset = 0;
        if(
          config.ansi_c.endianness ==
          configt::ansi_ct::endiannesst::IS_BIG_ENDIAN)
        {
          bit_offset = W - bf_width;
        }

        // Cast the union to a flat bitvector so that extractbits
        // (and, on the write side, update_bits) operate on a
        // bitvector type as they require.
        typecast_exprt bv_op{op, bv_typet{W}};
        expr = extractbits_exprt{
          std::move(bv_op),
          from_integer(bit_offset, c_index_type()),
          expr.type()};
      }
    }
  }
  else if(expr.id() == ID_union)
  {
    const union_exprt &union_expr = to_union_expr(expr);
    exprt offset = from_integer(0, c_index_type());
    side_effect_expr_nondett nondet(expr.type(), expr.source_location());
    expr = make_byte_update(nondet, offset, union_expr.op());
  }
}

void rewrite_union(exprt &expr)
{
  // Legacy overload without namespace — cannot handle big-endian
  // bit fields correctly. Use the namespacet overload when possible.
  symbol_tablet empty_symbol_table;
  const namespacet ns{empty_symbol_table};
  rewrite_union(expr, ns);
}

void rewrite_union(goto_functionst::goto_functiont &goto_function)
{
  symbol_tablet empty_symbol_table;
  const namespacet ns{empty_symbol_table};
  for(auto &instruction : goto_function.body.instructions)
  {
    rewrite_union(instruction.code_nonconst(), ns);

    if(instruction.has_condition())
      rewrite_union(instruction.condition_nonconst(), ns);
  }
}

void rewrite_union(goto_functionst &goto_functions)
{
  for(auto &gf_entry : goto_functions.function_map)
    rewrite_union(gf_entry.second);
}

void rewrite_union(goto_modelt &goto_model)
{
  const namespacet ns{goto_model.symbol_table};
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    for(auto &instruction : gf_entry.second.body.instructions)
    {
      rewrite_union(instruction.code_nonconst(), ns);

      if(instruction.has_condition())
        rewrite_union(instruction.condition_nonconst(), ns);
    }
  }
}

/// Undo the union access -> byte_extract replacement that rewrite_union did for
/// the purpose of displaying expressions to users.
/// \param expr: expression to inspect and possibly transform
/// \param ns: namespace
/// \return True if, and only if, the expression is unmodified
static bool restore_union_rec(exprt &expr, const namespacet &ns)
{
  bool unmodified = true;

  Forall_operands(it, expr)
    unmodified &= restore_union_rec(*it, ns);

  if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    byte_extract_exprt &be = to_byte_extract_expr(expr);
    if(be.op().type().id() == ID_union || be.op().type().id() == ID_union_tag)
    {
      const union_typet &union_type =
        be.op().type().id() == ID_union_tag
          ? ns.follow_tag(to_union_tag_type(be.op().type()))
          : to_union_type(be.op().type());

      for(const auto &comp : union_type.components())
      {
        if(be.offset() == 0 && be.type() == comp.type())
        {
          expr = member_exprt{be.op(), comp.get_name(), be.type()};
          return false;
        }
        else if(
          comp.type().id() == ID_array || comp.type().id() == ID_struct ||
          comp.type().id() == ID_struct_tag)
        {
          std::optional<exprt> result = get_subexpression_at_offset(
            member_exprt{be.op(), comp.get_name(), comp.type()},
            be.offset(),
            be.type(),
            ns);
          if(result.has_value())
          {
            expr = *result;
            return false;
          }
        }
      }
    }
  }

  return unmodified;
}

/// Undo the union access -> byte_extract replacement that rewrite_union did for
/// the purpose of displaying expressions to users.
/// \param expr: expression to inspect and possibly transform
/// \param ns: namespace
void restore_union(exprt &expr, const namespacet &ns)
{
  exprt tmp = expr;

  if(!restore_union_rec(tmp, ns))
    expr.swap(tmp);
}
