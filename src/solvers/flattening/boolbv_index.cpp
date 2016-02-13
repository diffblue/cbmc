/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/simplify_expr.h>
#include <util/i2string.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_index(const index_exprt &expr, bvt &bv)
{
  if(expr.id()!=ID_index)
    throw "expected index expression";

  if(expr.operands().size()!=2)
    throw "index takes two operands";
    
  const exprt &array=expr.array();
  const exprt &index=expr.index();
  
  const typet &array_op_type=ns.follow(array.type());
  
  if(array_op_type.id()==ID_array)
  {
    const array_typet &array_type=
      to_array_type(array_op_type);

    unsigned width=boolbv_width(expr.type());
    
    if(width==0)
      return conversion_failed(expr, bv);
    
    // see if the array size is constant

    if(is_unbounded_array(array_type))
    {
      // use array decision procedure
    
      // free variables

      bv.resize(width);
      for(unsigned i=0; i<width; i++)
        bv[i]=prop.new_variable();

      record_array_index(expr);

      // record type if array is a symbol

      if(array.id()==ID_symbol)
        map.get_map_entry(
          to_symbol_expr(array).get_identifier(), array_type);

      // make sure we have the index in the cache
      convert_bv(index);
      
      return;
    }

    // Must have a finite size
    mp_integer array_size;
    if(to_integer(array_type.size(), array_size))
      throw "failed to convert array size";
    
    // see if the index address is constant
    // many of these are compacted by simplify_expr
    // but variable location writes will block this
    mp_integer index_value;
    if(!to_integer(index, index_value))
      return convert_index(array, index_value, bv);

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
        i2string(uniform_array_counter++);

      symbol_exprt result(identifier, expr.type());
      bv = convert_bv(result);
      
      equal_exprt value_equality(result, array.op0());
      
      binary_relation_exprt lower_bound(from_integer(0, index.type()), ID_le, index);
      binary_relation_exprt upper_bound(index, ID_lt, from_integer(array_size, index.type()));

      if(lower_bound.lhs().is_nil() ||
         upper_bound.rhs().is_nil())
        throw "number conversion failed (2)";

      and_exprt range_condition(lower_bound, upper_bound);
      implies_exprt implication(range_condition, value_equality);
      
      // Simplify may remove the lower bound if the type
      // is correct.
      prop.l_set_to_true(convert(simplify_expr(implication, ns)));
      return;
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
        i2string(actual_array_counter++);

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

        if(index_equality.rhs().is_nil())
          throw "number conversion failed (1)";

        assert(it != array.operands().end());
        
        value_equality.rhs()=*it++;

        // Cache comparisons and equalities
        prop.l_set_to_true(convert(implies_exprt(index_equality,
                                                 value_equality)));
      }
      
      return;
    }
      
#endif
      
      
    // TODO : As with constant index, there is a trade-off
    // of when it is best to flatten the whole array and
    // when it is best to use the array theory and then use
    // one or more of the above encoding strategies.
      
    // get literals for the whole array

    const bvt &array_bv=convert_bv(array);

    if(array_size*width!=array_bv.size())
      throw "unexpected array size";
      
    // TODO: maybe a shifter-like construction would be better
    // Would be a lot more compact but propagate worse

    if(prop.has_set_to())
    {
      // free variables

      bv.resize(width);
      for(unsigned i=0; i<width; i++)
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

        if(index_equality.rhs().is_nil())
          throw "number conversion failed (1)";

        mp_integer offset=i*width;

        for(unsigned j=0; j<width; j++)
          equal_bv[j]=prop.lequal(bv[j],
                             array_bv[integer2long(offset+j)]);

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
      
      assert(array_size>0);

      for(mp_integer i=0; i<array_size; i=i+1)
      {
        equality.op1()=from_integer(i, constant_type);
          
        literalt e=convert(equality);

        mp_integer offset=i*width;

        for(unsigned j=0; j<width; j++)
        {
          literalt l=array_bv[integer2long(offset+j)];

          if(i==0) // this initializes bv
            bv[j]=l;
          else
            bv[j]=prop.lselect(e, l, bv[j]);
        }
      }    
    }
  }
  else
    return conversion_failed(expr, bv);
}

/*******************************************************************\

Function: boolbvt::convert_index

  Inputs:

 Outputs:

 Purpose: index operator with constant index

\*******************************************************************/

void boolbvt::convert_index(
  const exprt &array,
  const mp_integer &index,
  bvt &bv)
{
  const array_typet &array_type=
    to_array_type(ns.follow(array.type()));

  unsigned width=boolbv_width(array_type.subtype());

  if(width==0)
    return conversion_failed(array, bv);

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
    for(unsigned i=0; i<width; i++)
      bv[i]=tmp[integer2long(offset+i)];
  }
  else
  {
    // out of bounds
    for(unsigned i=0; i<width; i++)
      bv[i]=prop.new_variable();
  }
}
