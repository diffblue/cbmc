/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <solvers/lowering/expr_lowering.h>

bvt boolbvt::convert_index(const index_exprt &expr)
{
  const exprt &array=expr.array();
  const exprt &index=expr.index();

  const typet &array_op_type = array.type();

  bvt bv;

  if(array_op_type.id()==ID_array)
  {
    const array_typet &array_type=
      to_array_type(array_op_type);

    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    // see if the array size is constant

    if(is_unbounded_array(array_type))
    {
      // use array decision procedure

      if(has_byte_operator(expr))
      {
        const index_exprt final_expr =
          to_index_expr(lower_byte_operators(expr, ns));
        CHECK_RETURN(final_expr != expr);
        bv = convert_bv(final_expr);

        // record type if array is a symbol
        const exprt &final_array = final_expr.array();
        if(
          final_array.id() == ID_symbol || final_array.id() == ID_nondet_symbol)
        {
          std::size_t width = boolbv_width(array_type);
          (void)map.get_literals(
            final_array.get(ID_identifier), array_type, width);
        }

        // make sure we have the index in the cache
        convert_bv(final_expr.index());
      }
      else
      {
        // free variables
        bv = prop.new_variables(width);

        record_array_index(expr);

        // record type if array is a symbol
        if(array.id() == ID_symbol || array.id() == ID_nondet_symbol)
        {
          std::size_t width = boolbv_width(array_type);
          (void)map.get_literals(array.get(ID_identifier), array_type, width);
        }

        // make sure we have the index in the cache
        convert_bv(index);
      }

      return bv;
    }

    // Must have a finite size
    mp_integer array_size =
      numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));

    {
      // see if the index address is constant
      // many of these are compacted by simplify_expr
      // but variable location writes will block this
      auto maybe_index_value = numeric_cast<mp_integer>(index);
      if(maybe_index_value.has_value())
      {
        return convert_index(array, maybe_index_value.value());
      }
    }

    // Special case : arrays of one thing (useful for constants)
    // TODO : merge with ACTUAL_ARRAY_HACK so that ranges of the same
    // value, bit-patterns with the same value, etc. are treated like
    // this rather than as a series of individual options.
    #define UNIFORM_ARRAY_HACK
    #ifdef UNIFORM_ARRAY_HACK
    bool is_uniform = array.id() == ID_array_of;

    if(array.id() == ID_constant || array.id() == ID_array)
    {
      is_uniform = array.operands().size() <= 1 ||
                   std::all_of(
                     ++array.operands().begin(),
                     array.operands().end(),
                     [&array](const exprt &expr) {
                       return expr == to_multi_ary_expr(array).op0();
                     });
    }

    if(is_uniform && prop.has_set_to())
    {
      static int uniform_array_counter;  // Temporary hack

      const std::string identifier = CPROVER_PREFIX "internal_uniform_array_" +
                                     std::to_string(uniform_array_counter++);

      symbol_exprt result(identifier, expr.type());
      bv = convert_bv(result);

      // return an unconstrained value in case of an empty array (the access is
      // necessarily out-of-bounds)
      if(!array.has_operands())
        return bv;

      equal_exprt value_equality(result, to_multi_ary_expr(array).op0());

      binary_relation_exprt lower_bound(
        from_integer(0, index.type()), ID_le, index);
      binary_relation_exprt upper_bound(
        index, ID_lt, from_integer(array_size, index.type()));

      and_exprt range_condition(std::move(lower_bound), std::move(upper_bound));
      implies_exprt implication(
        std::move(range_condition), std::move(value_equality));

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

      const std::string identifier = CPROVER_PREFIX "internal_actual_array_" +
                                     std::to_string(actual_array_counter++);

      symbol_exprt result(identifier, expr.type());
      bv = convert_bv(result);

      // add implications

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
      bv_utils.equal_const_register(convert_bv(result)); // Maybe
#endif

      exprt::operandst::const_iterator it = array.operands().begin();

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        INVARIANT(
          it != array.operands().end(),
          "this loop iterates over the array, so `it` shouldn't be increased "
          "past the array's end");

        // Cache comparisons and equalities
        prop.l_set_to_true(convert(implies_exprt(
          equal_exprt(index, from_integer(i, index.type())),
          equal_exprt(result, *it++))));
      }

      return bv;
    }

#endif


    // TODO : As with constant index, there is a trade-off
    // of when it is best to flatten the whole array and
    // when it is best to use the array theory and then use
    // one or more of the above encoding strategies.

    // get literals for the whole array

    const bvt &array_bv =
      convert_bv(array, numeric_cast_v<std::size_t>(array_size * width));

    // TODO: maybe a shifter-like construction would be better
    // Would be a lot more compact but propagate worse

    if(prop.has_set_to())
    {
      // free variables
      bv = prop.new_variables(width);

      // add implications

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
#endif

      bvt equal_bv;
      equal_bv.resize(width);

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        mp_integer offset=i*width;

        for(std::size_t j=0; j<width; j++)
          equal_bv[j] = prop.lequal(
            bv[j], array_bv[numeric_cast_v<std::size_t>(offset + j)]);

        prop.l_set_to_true(prop.limplies(
          convert(equal_exprt(index, from_integer(i, index.type()))),
          prop.land(equal_bv)));
      }
    }
    else
    {
      bv.resize(width);

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
#endif

      typet constant_type=index.type(); // type of index operand

      DATA_INVARIANT(
        array_size > 0,
        "non-positive array sizes are forbidden in goto programs");

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        literalt e =
          convert(equal_exprt(index, from_integer(i, constant_type)));

        mp_integer offset=i*width;

        for(std::size_t j=0; j<width; j++)
        {
          literalt l = array_bv[numeric_cast_v<std::size_t>(offset + j)];

          if(i==0) // this initializes bv
            bv[j]=l;
          else
            bv[j]=prop.lselect(e, l, bv[j]);
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
  const array_typet &array_type = to_array_type(array.type());

  std::size_t width = boolbv_width(array_type.element_type());

  if(width==0)
    return conversion_failed(array);

  // TODO: If the underlying array can use one of the
  // improvements given above then it may be better to use
  // the array theory for short chains of updates and then
  // the improved array handling rather than full flattening.
  // Note that the calculation is non-trivial as the cost of
  // full flattening is amortised against all uses of
  // the array (constant and variable indexes) and updated
  // versions of it.

  const bvt &tmp=convert_bv(array); // recursive call

  mp_integer offset=index*width;

  if(offset>=0 &&
     offset+width<=mp_integer(tmp.size()))
  {
    // in bounds

    // The assertion below is disabled as we want to be able
    // to run CBMC without simplifier.
    // Expression simplification should remove these cases
    // assert(array.id()!=ID_array_of &&
    //       array.id()!=ID_array);
    // If not there are large improvements possible as above

    std::size_t offset_int = numeric_cast_v<std::size_t>(offset);
    return bvt(tmp.begin() + offset_int, tmp.begin() + offset_int + width);
  }
  else if(array.id() == ID_member || array.id() == ID_index)
  {
    // out of bounds for the component, but not necessarily outside the bounds
    // of the underlying object
    object_descriptor_exprt o;
    o.build(array, ns);
    CHECK_RETURN(o.offset().id() != ID_unknown);

    const auto subtype_bytes_opt =
      pointer_offset_size(array_type.element_type(), ns);
    CHECK_RETURN(subtype_bytes_opt.has_value());

    exprt new_offset = simplify_expr(
      plus_exprt(
        o.offset(), from_integer(index * (*subtype_bytes_opt), o.offset().type())),
      ns);

    byte_extract_exprt be =
      make_byte_extract(o.root_object(), new_offset, array_type.element_type());

    return convert_bv(be);
  }
  else if(
    array.id() == ID_byte_extract_big_endian ||
    array.id() == ID_byte_extract_little_endian)
  {
    const byte_extract_exprt &byte_extract_expr = to_byte_extract_expr(array);

    const auto subtype_bytes_opt =
      pointer_offset_size(array_type.element_type(), ns);
    CHECK_RETURN(subtype_bytes_opt.has_value());

    // add offset to index
    exprt new_offset = simplify_expr(
      plus_exprt{
        byte_extract_expr.offset(),
        from_integer(
          index * (*subtype_bytes_opt), byte_extract_expr.offset().type())},
      ns);

    byte_extract_exprt be = byte_extract_expr;
    be.offset() = new_offset;
    be.type() = array_type.element_type();

    return convert_bv(be);
  }
  else
  {
    // out of bounds
    return prop.new_variables(width);
  }
}
