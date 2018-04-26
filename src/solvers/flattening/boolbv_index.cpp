/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <cassert>

#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

bvt boolbvt::convert_index(const index_exprt &expr)
{
  const exprt &array=expr.array();
  const exprt &index=expr.index();

  const typet &array_op_type=ns.follow(array.type());

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
    mp_integer array_size = numeric_cast_v<mp_integer>(array_type.size());
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
    bool is_uniform = false;

    if(array.id()==ID_array_of)
    {
      is_uniform = true;
    }
    else if(array.id()==ID_constant || array.id()==ID_array)
    {
      bool found_exception = false;
      forall_expr(it, array.operands())
      {
        if(*it != array.op0())
        {
          found_exception = true;
          break;
        }
      }

      if(!found_exception)
        is_uniform = true;
    }

    if(is_uniform && prop.has_set_to())
    {
      static int uniform_array_counter;  // Temporary hack

      std::string identifier=
        "__CPROVER_internal_uniform_array_"+
        std::to_string(uniform_array_counter++);

      symbol_exprt result(identifier, expr.type());
      bv = convert_bv(result);

      equal_exprt value_equality(result, array.op0());

      binary_relation_exprt lower_bound(
        from_integer(0, index.type()), ID_le, index);
      CHECK_RETURN(lower_bound.lhs().is_not_nil());
      binary_relation_exprt upper_bound(
        index, ID_lt, from_integer(array_size, index.type()));
      CHECK_RETURN(upper_bound.rhs().is_not_nil());

      and_exprt range_condition(lower_bound, upper_bound);
      implies_exprt implication(range_condition, value_equality);

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

      std::string identifier=
        "__CPROVER_internal_actual_array_"+
        std::to_string(actual_array_counter++);

      symbol_exprt result(identifier, expr.type());
      bv = convert_bv(result);

      // add implications

      equal_exprt index_equality;
      index_equality.lhs()=index; // index operand

      equal_exprt value_equality;
      value_equality.lhs()=result;

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
      bv_utils.equal_const_register(convert_bv(result)); // Maybe
#endif

      exprt::operandst::const_iterator it = array.operands().begin();

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        index_equality.rhs()=from_integer(i, index_equality.lhs().type());
        CHECK_RETURN(index_equality.rhs().is_not_nil());

        INVARIANT(
          it != array.operands().end(),
          "this loop iterates over the array, so `it` shouldn't be increased "
          "past the array's end");

        value_equality.rhs()=*it++;

        // Cache comparisons and equalities
        prop.l_set_to_true(convert(implies_exprt(index_equality,
                                                 value_equality)));
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

      bv.resize(width);
      for(std::size_t i=0; i<width; i++)
        bv[i]=prop.new_variable();

      // add implications

      equal_exprt index_equality;
      index_equality.lhs()=index; // index operand

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
#endif

      bvt equal_bv;
      equal_bv.resize(width);

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        index_equality.rhs()=from_integer(i, index_equality.lhs().type());
        CHECK_RETURN(index_equality.rhs().is_not_nil());

        mp_integer offset=i*width;

        for(std::size_t j=0; j<width; j++)
          equal_bv[j]=prop.lequal(bv[j],
                             array_bv[integer2size_t(offset+j)]);

        prop.l_set_to_true(
          prop.limplies(convert(index_equality), prop.land(equal_bv)));
      }
    }
    else
    {
      bv.resize(width);

      equal_exprt equality;
      equality.lhs()=index; // index operand

#ifdef COMPACT_EQUAL_CONST
      bv_utils.equal_const_register(convert_bv(index));  // Definitely
#endif

      typet constant_type=index.type(); // type of index operand

      DATA_INVARIANT(
        array_size > 0,
        "non-positive array sizes are forbidden in goto programs");

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        equality.op1()=from_integer(i, constant_type);

        literalt e=convert(equality);

        mp_integer offset=i*width;

        for(std::size_t j=0; j<width; j++)
        {
          literalt l=array_bv[integer2size_t(offset+j)];

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
  const array_typet &array_type=
    to_array_type(ns.follow(array.type()));

  std::size_t width=boolbv_width(array_type.subtype());

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

    const auto subtype_bytes_opt =
      pointer_offset_size(array_type.subtype(), ns);
    CHECK_RETURN(subtype_bytes_opt.has_value());

    exprt new_offset = simplify_expr(
      plus_exprt(
        o.offset(), from_integer(index * (*subtype_bytes_opt), o.offset().type())),
      ns);

    byte_extract_exprt be(
      byte_extract_id(), o.root_object(), new_offset, array_type.subtype());

    return convert_bv(be);
  }
  else
  {
    // out of bounds
    for(std::size_t i=0; i<width; i++)
      bv[i]=prop.new_variable();
  }

  return bv;
}
