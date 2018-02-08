/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <algorithm>
#include <cassert>

#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

/// \param array: an array expression
/// \return true if all elements are equal
static bool is_uniform(const exprt &array)
{
  if(array.id() == ID_array_of)
    return true;
  if(array.id() == ID_constant || array.id() == ID_array)
  {
    return std::all_of(
      array.operands().begin(),
      array.operands().end(),
      [&](const exprt &expr) { // NOLINT
        return expr == array.op0();
      });
  }
  return false;
}

bvt boolbvt::convert_index(const index_exprt &expr)
{
  const exprt &array=expr.array();
  const exprt &index=expr.index();
  const typet &array_op_type=ns.follow(array.type());
  bvt bv;

  if(array_op_type.id()==ID_array)
  {
    const array_typet &array_type = to_array_type(array_op_type);
    const std::size_t width = boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    // see if the array size is constant
    if(is_unbounded_array(array_type))
    {
      // use array decision procedure

      // free variables
      bv.resize(width);
      for(std::size_t i=0; i<width; i++)
        bv[i]=prop.new_variable();

      record_array_index(expr);

      // record type if array is a symbol
      if(array.id()==ID_symbol)
        map.get_map_entry(
          to_symbol_expr(array).get_identifier(), array_type);

      // make sure we have the index in the cache
      convert_bv(index);
      return bv;
    }

    // Must have a finite size
    const auto array_size = numeric_cast_v<mp_integer>(array_type.size());

    // see if the index address is constant
    // many of these are compacted by simplify_expr
    // but variable location writes will block this
    if(const auto index_value = numeric_cast<mp_integer>(index))
      return convert_index(array, *index_value);

    // Special case : arrays of one thing (useful for constants)
    // TODO : merge with ACTUAL_ARRAY_HACK so that ranges of the same
    // value, bit-patterns with the same value, etc. are treated like
    // this rather than as a series of individual options.
    #define UNIFORM_ARRAY_HACK
    #ifdef UNIFORM_ARRAY_HACK
    if(is_uniform(array) && prop.has_set_to())
    {
      static int uniform_array_counter;  // Temporary hack

      const std::string identifier = "__CPROVER_internal_uniform_array_" +
                                     std::to_string(uniform_array_counter++);

      const symbol_exprt result(identifier, expr.type());
      bv = convert_bv(result);

      const equal_exprt value_equality(result, array.op0());

      const binary_relation_exprt lower_bound(
        from_integer(0, index.type()), ID_le, index);
      const binary_relation_exprt upper_bound(
        index, ID_lt, from_integer(array_size, index.type()));

      const and_exprt range_condition(lower_bound, upper_bound);
      const implies_exprt implication(range_condition, value_equality);

      // Simplify may remove the lower bound if the type
      // is correct.
      prop.l_set_to_true(convert(simplify_expr(implication, ns)));

      return bv;
    }
    #endif

    #define ACTUAL_ARRAY_HACK
    #ifdef ACTUAL_ARRAY_HACK
    // More useful when updates to concrete locations in
    // actual arrays are compacted by simplify_expr
    if((array.id()==ID_constant || array.id()==ID_array) &&
       prop.has_set_to())
    {
      #ifdef CONSTANT_ARRAY_HACK
      // TODO : Compile the whole array into a single relation
      #endif

      // Symbol for output
      static int actual_array_counter;  // Temporary hack

      const std::string identifier = "__CPROVER_internal_actual_array_" +
                                     std::to_string(actual_array_counter++);

      const symbol_exprt result(identifier, expr.type());
      bv = convert_bv(result);

      INVARIANT(
        array_size <= array.operands().size(),
        "size should not exceed number of operands");

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
      bv_utils.equal_const_register(convert_bv(result)); // Maybe
#endif

      for(std::size_t i = 0; i < array_size; ++i)
      {
        const equal_exprt index_equality(index, from_integer(i, index.type()));
        const equal_exprt value_equality(result, array.operands()[i]);
        prop.l_set_to_true(
          convert(implies_exprt(index_equality, value_equality)));
      }

      return bv;
    }

#endif

    // TODO : As with constant index, there is a trade-off
    // of when it is best to flatten the whole array and
    // when it is best to use the array theory and then use
    // one or more of the above encoding strategies.

    // get literals for the whole array
    const bvt &array_bv=convert_bv(array);
    CHECK_RETURN(array_size * width == array_bv.size());

    // TODO: maybe a shifter-like construction would be better
    // Would be a lot more compact but propagate worse

    if(prop.has_set_to())
    {
      // free variables
      bv.resize(width);
      for(std::size_t i=0; i<width; i++)
        bv[i]=prop.new_variable();


#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
#endif

      bvt equal_bv;
      equal_bv.resize(width);

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        const equal_exprt index_equality(index, from_integer(i, index.type()));
        mp_integer offset=i*width;

        for(std::size_t j=0; j<width; j++)
          equal_bv[j] =
            prop.lequal(bv[j], array_bv[integer2size_t(offset + j)]);

        prop.l_set_to_true(
          prop.limplies(convert(index_equality), prop.land(equal_bv)));
      }
    }
    else
    {
      bv.resize(width);
      const typet index_type = index.type();
      INVARIANT(array_size > 0, "array size should be positive");

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
#endif

      for(mp_integer i = 0; i < array_size; ++i)
      {
        const equal_exprt equality(index, from_integer(i, index_type));
        const literalt e = convert(equality);
        const mp_integer offset = i * width;
        for(std::size_t j = 0; j < width; ++j)
        {
          literalt l=array_bv[integer2size_t(offset+j)];
          // for 0 only initializes bv
          bv[j] = i == 0 ? l : prop.lselect(e, l, bv[j]);
        }
      }
    }
  }
  else
    return conversion_failed(expr);

  return bv;
}

/// index operator with constant index
bvt boolbvt::convert_index(
  const exprt &array,
  const mp_integer &index)
{
  const array_typet &array_type = to_array_type(ns.follow(array.type()));
  const std::size_t width = boolbv_width(array_type.subtype());
  if(width==0)
    return conversion_failed(array);
  bvt bv;
  bv.resize(width);

  // TODO: If the underlying array can use one of the
  // improvements given above then it may be better to use
  // the array theory for short chains of updates and then
  // the improved array handling rather than full flattening.
  // Note that the calculation is non-trivial as the cost of
  // full flattening is amortised against all uses of
  // the array (constant and variable indexes) and updated
  // versions of it.

  const bvt &tmp = convert_bv(array);
  const mp_integer offset = index * width;
  const bool in_bounds =
    offset >= 0 && offset + width <= mp_integer(tmp.size());
  if(in_bounds)
  {
    // The assertion below is disabled as we want to be able
    // to run CBMC without simplifier.
    // Expression simplification should remove these cases
    // If not there are large improvements possible as above

    for(std::size_t i=0; i<width; i++)
      bv[i]=tmp[integer2size_t(offset+i)];
  }
  else if(
    array.id() == ID_member || array.id() == ID_index ||
    array.id() == ID_byte_extract_big_endian ||
    array.id() == ID_byte_extract_little_endian)
  {
    object_descriptor_exprt o;
    o.build(array, ns);
    CHECK_RETURN(o.offset().id() != ID_unknown);

    const mp_integer subtype_bytes =
      pointer_offset_size(array_type.subtype(), ns);
    const exprt new_offset = simplify_expr(
      plus_exprt(
        o.offset(), from_integer(index * subtype_bytes, o.offset().type())),
      ns);

    const byte_extract_exprt be(
      byte_extract_id(), o.root_object(), new_offset, array_type.subtype());

    return convert_bv(be);
  }
  else
  {
    for(std::size_t i=0; i<width; i++)
      bv[i]=prop.new_variable();
  }

  return bv;
}
