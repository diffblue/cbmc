/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>

#include <ansi-c/c_types.h>

#if 0

#include <cassert>
#include <cstdlib>

#include <util/c_misc.h>
#include <util/base_type.h>
#include <util/arith_tools.h>
#include <util/rename.h>
#include <util/i2string.h>
#include <util/array_name.h>
#include <util/config.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/symbol_table.h>
#include <util/guard.h>
#include <util/options.h>
#include <util/pointer_predicates.h>
#include <util/byte_operators.h>

#include <ansi-c/c_typecast.h>

#include <pointer-analysis/value_set.h>

#include <langapi/language_util.h>
#endif

#include "dereference.h"

/*******************************************************************\

Function: dereferencet::operator()

  Inputs: expression, to be dereferenced

 Outputs: returns object after dereferencing

 Purpose:

\*******************************************************************/

exprt dereferencet::operator()(const exprt &pointer)
{
  if(pointer.type().id()!=ID_pointer)
    throw "dereference expected pointer type, but got "+
          pointer.type().pretty();  

  // we may get ifs
  if(pointer.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(pointer);

    // push down the if, do recursive call
    exprt true_case=operator()(if_expr.true_case());
    exprt false_case=operator()(if_expr.false_case());
    
    return if_exprt(if_expr.cond(), true_case, false_case);
  }
  
  // type of the object
  const typet &type=pointer.type().subtype();

  #if 0
  std::cout << "DEREF: " << from_expr(ns, "", pointer) << std::endl;
  #endif

  return dereference_rec(
    pointer,
    gen_zero(index_type()), // offset
    type);
}

/*******************************************************************\

Function: dereferencet::read_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dereferencet::read_object(
  const exprt &object,
  const exprt &offset,
  const typet &type)
{
  const typet &object_type=ns.follow(object.type());
  const typet &dest_type=ns.follow(type);

  // is the object an array with matching subtype?
  
  // check if offset is zero
  if(offset.is_zero())
  {
    // check type
    if(object_type==dest_type)
    {
      return object; // trivial case
    }
    else if(type_compatible(object_type, dest_type))
    {
      // the type differs, but we can do this with a typecast
      return typecast_exprt(object, dest_type);
    }
  }
  
  if(object.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(object);
    
    exprt index=index_expr.index();
    
    // multiply index by object size
    exprt size=size_of_expr(object_type, ns);

    if(size.is_nil())
      throw "dereference failed to get object size for index";
      
    index.make_typecast(offset.type());
    size.make_typecast(index.type());
      
    exprt new_offset=plus_exprt(offset, mult_exprt(index, size));

    return read_object(index_expr.array(), new_offset, type);
  }
  
  // give up and use byte_extract
  return binary_exprt(object, byte_extract_id(), offset, dest_type);
}

/*******************************************************************\

Function: dereferencet::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dereferencet::dereference_rec(
  const exprt &address,
  const exprt &offset,
  const typet &type)
{
  if(address.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(address);
    
    const exprt &object=address_of_expr.object();

    return read_object(object, offset, type);    
  }
  else if(address.id()==ID_typecast)
  {
    const exprt &op=to_typecast_expr(address).op();
    const typet &op_type=ns.follow(op.type());
    
    // pointer type cast?
    if(op_type.id()==ID_pointer)
      return dereference_rec(op, offset, type); // just pass down
    else if(op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv)
    {
      // integer address
      throw "dereferencet: integer address unhandled";
    }
    else
      throw "dereferencet: unexpected cast";
  }
  else if(address.id()==ID_plus)
  {
    // pointer arithmetic
    if(address.operands().size()<2)
      throw "plus with less than two operands";
    
    if(address.operands().size()>2)
      return dereference_rec(make_binary(address), offset, type);

    // binary
    exprt pointer=address.op0(), integer=address.op1();
    
    if(ns.follow(integer.type()).id()==ID_pointer)
      std::swap(pointer, integer);

    // multiply integer by object size
    exprt size=size_of_expr(pointer.type().subtype(), ns);
    if(size.is_nil())
      throw "dereference failed to get object size for pointer arithmetic";

    // make types of offset and size match
    if(size.type()!=integer.type())
      integer.make_typecast(size.type());
  
    exprt new_offset=plus_exprt(offset, mult_exprt(size, integer));

    return dereference_rec(pointer, new_offset, type);
  }
  else if(address.id()==ID_constant)
  {
    // pointer-typed constant
    if(to_constant_expr(address).get_value()==ID_NULL) // NULL
    {
      return exprt(ID_null_object, ns.follow(address.type()).subtype());
    }
    else
      throw "dereferencet: unexpected pointer constant "+address.pretty();
  }
  else
  {
    throw "failed to dereference `"+address.id_string()+"'";
  }
}

/*******************************************************************\

Function: dereferencet::type_compatible

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dereferencet::type_compatible(
  const typet &object_type,
  const typet &dereference_type) const
{
  if(dereference_type.id()==ID_empty)
    return true; // always ok

  if(object_type==dereference_type)
    return true; // ok, they just match

  // check for struct prefixes

  if(object_type.id()==ID_struct &&
     dereference_type.id()==ID_struct)
  {
    if(to_struct_type(dereference_type).is_prefix_of(
         to_struct_type(object_type)))
      return true; // ok, dreference_type is a prefix of object_type
  }

  // any code is ok
  if(dereference_type.id()==ID_code &&
     object_type.id()==ID_code)
    return true;

  // vectors of same size are ok
  if((object_type.id()==ID_signedbv || object_type.id()==ID_unsignedbv) &&
     (dereference_type.id()==ID_signedbv || dereference_type.id()==ID_unsignedbv))
  {
    return object_type.get(ID_width)==dereference_type.get(ID_width);
  }

  // pointer to pointer is always ok
  if(object_type.id()==ID_pointer &&
     dereference_type.id()==ID_pointer)
    return true;

  // really different

  return false;
}

#if 0
#include "pointer_offset_sum.h"

/*******************************************************************\

Function: dereferencet::get_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt &dereferencet::get_symbol(const exprt &expr)
{
  if(expr.id()==ID_member || expr.id()==ID_index)
    return get_symbol(expr.op0());
  
  return expr;
}

/*******************************************************************\

Function: dereferencet::invalid_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dereferencet::invalid_pointer(
  const exprt &pointer,
  const guardt &guard)
{
  if(!options.get_bool_option("pointer-check"))
    return;
    
  // constraint that it actually is an invalid pointer
  guardt tmp_guard(guard);
  tmp_guard.add(::invalid_pointer(pointer));
  
  dereference_callback.dereference_failure(
    "pointer dereference",
    "invalid pointer", 
    tmp_guard);
}

/*******************************************************************\

Function: dereferencet::build_reference_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dereferencet::valuet dereferencet::build_reference_to(
  const exprt &what,
  const modet mode,
  const exprt &pointer_expr,
  const guardt &guard)
{
  const typet &dereference_type=
    ns.follow(pointer_expr.type()).subtype();

  if(what.id()==ID_unknown ||
     what.id()==ID_invalid)
  {
    invalid_pointer(pointer_expr, guard);
    return valuet();
  }
  
  if(what.id()!=ID_object_descriptor)
    throw "unknown points-to: "+what.id_string();
  
  const object_descriptor_exprt &o=to_object_descriptor_expr(what);

  const exprt &root_object=o.root_object();
  const exprt &object=o.object();
  
  #if 0
  std::cout << "O: " << from_expr(ns, "", root_object) << std::endl;
  #endif
  
  valuet result;
  
  if(root_object.id()=="NULL-object")
  {
    if(options.get_bool_option("pointer-check"))
    {
      guardt tmp_guard(guard);
      
      if(o.offset().is_zero())
      {
        tmp_guard.add(null_pointer(pointer_expr));

        dereference_callback.dereference_failure(
          "pointer dereference",
          "NULL pointer", tmp_guard);
      }
      else
      {
        tmp_guard.add(null_object(pointer_expr));

        dereference_callback.dereference_failure(
          "pointer dereference",
          "NULL plus offset pointer", tmp_guard);
      }
    }
  }
  else if(root_object.id()==ID_dynamic_object)
  {
    //const dynamic_object_exprt &dynamic_object=
    //  to_dynamic_object_expr(root_object);

    // the object produced by malloc
    exprt malloc_object=
      ns.lookup(CPROVER_PREFIX "malloc_object").symbol_expr();

    exprt is_malloc_object=same_object(pointer_expr, malloc_object);

    // constraint that it actually is a dynamic object
    exprt dynamic_object_expr(ID_dynamic_object, bool_typet());
    dynamic_object_expr.copy_to_operands(pointer_expr);
    
    // this is also our guard
    result.pointer_guard=dynamic_object_expr;
    
    // can't remove here, turn into *p
    result.value=dereference_exprt(pointer_expr, dereference_type);

    if(options.get_bool_option("pointer-check"))
    {
      //if(!dynamic_object.valid().is_true())
      {
        // check if it is still alive
        guardt tmp_guard(guard);
        tmp_guard.add(deallocated(pointer_expr, ns));
        dereference_callback.dereference_failure(
          "pointer dereference",
          "dynamic object deallocated", 
          tmp_guard);
      }

      if(options.get_bool_option("bounds-check"))
      {
        if(!o.offset().is_zero())
        {
          // check lower bound
          guardt tmp_guard(guard);
          tmp_guard.add(is_malloc_object);
          tmp_guard.add(dynamic_object_lower_bound(pointer_expr));
          dereference_callback.dereference_failure(
            "pointer dereference",
            "dynamic object lower bound", tmp_guard);
        }

        {
          // check upper bound
          
          // we check SAME_OBJECT(__CPROVER_malloc_object, p) &&
          //          POINTER_OFFSET(p)+size>__CPROVER_malloc_size

          guardt tmp_guard(guard);
          tmp_guard.add(is_malloc_object);
          tmp_guard.add(dynamic_object_upper_bound(pointer_expr, dereference_type, ns));
          dereference_callback.dereference_failure(
            "pointer dereference",
            "dynamic object upper bound", tmp_guard);
        }
      }
    }
  }
  else if(root_object.id()==ID_integer_address)
  {
    // This is stuff like *((char *)5).
    // This is turned into an access to __CPROVER_memory[...].

    const symbolt &memory_symbol=ns.lookup(CPROVER_PREFIX "memory");    
    exprt symbol_expr=symbol_exprt(memory_symbol.name, memory_symbol.type);

    exprt pointer_offset=unary_exprt(
      ID_pointer_offset, pointer_expr, index_type());

    if(base_type_eq(
         ns.follow(memory_symbol.type).subtype(), 
         dereference_type, ns))
    {
      // Types match already, what a coincidence!
      // We can use an index expression.

      exprt index_expr=index_exprt(symbol_expr, pointer_offset);
      index_expr.type()=ns.follow(memory_symbol.type).subtype();
      result.value=index_expr;
    }
    else
    {
      // We need to use byte_extract.
      // Won't do this without a committment to an endianness.

      if(config.ansi_c.endianness==configt::ansi_ct::NO_ENDIANNESS)
      {
      }
      else
      {
        exprt byte_extract(byte_extract_id(), dereference_type);
        byte_extract.copy_to_operands(symbol_expr, pointer_offset);
        result.value=byte_extract;
      }
    }
  }
  else
  {
    // something generic -- really has to be a symbol
    address_of_exprt object_pointer(object);
    
    if(o.offset().is_zero())
    {
      equal_exprt equality(pointer_expr, object_pointer);

      if(ns.follow(equality.lhs().type())!=ns.follow(equality.rhs().type()))
        equality.lhs().make_typecast(equality.rhs().type());

      result.pointer_guard=equality;
    }
    else
    {
      result.pointer_guard=same_object(pointer_expr, object_pointer);
    }
    
    guardt tmp_guard(guard);
    tmp_guard.add(result.pointer_guard);
    
    valid_check(object, tmp_guard, mode);
    
    const typet &object_type=ns.follow(object.type());
    const exprt &root_object=o.root_object();
    const typet &root_object_type=ns.follow(root_object.type());
    
    if(dereference_type_compare(object_type, dereference_type) && 
       o.offset().is_zero())
    {
      // The simplest case: types match, and offset is zero!
      // This is great, we are almost done.

      result.value=object;

      if(object_type!=ns.follow(dereference_type))
        result.value.make_typecast(dereference_type);
    }
    else if(root_object_type.id()==ID_array &&
            dereference_type_compare(root_object_type.subtype(), dereference_type))
    {
      // We have an array with a subtype that matches
      // the dereferencing type.
      // We will require well-alignedness!
      
      exprt offset;

      // this should work as the object is essentially the root object    
      if(o.offset().is_constant())
        offset=o.offset();
      else
        offset=unary_exprt(ID_pointer_offset, pointer_expr, index_type());

      exprt adjusted_offset;
      
      // are we doing a byte?
      mp_integer element_size=
        pointer_offset_size(ns, dereference_type);
          
      if(element_size==1)
      {
        // no need to adjust offset
        adjusted_offset=offset;
      }
      else
      {
        exprt element_size_expr=
          from_integer(element_size, offset.type());
          
        adjusted_offset=binary_exprt(
          offset, ID_div, element_size_expr, offset.type());
          
        // TODO: need to assert well-alignedness
      }
      
      index_exprt index_expr=
        index_exprt(root_object, adjusted_offset, root_object_type.subtype());

      bounds_check(index_expr, tmp_guard);
      
      result.value=index_expr;

      if(ns.follow(result.value.type())!=ns.follow(dereference_type))
        result.value.make_typecast(dereference_type);
    }
    else
    {
      // we extract something from the root object
      result.value=o.root_object();

      // this is relative to the root object
      const exprt offset=
        unary_exprt(ID_pointer_offset, pointer_expr, index_type());

      if(memory_model(result.value, dereference_type, tmp_guard, offset))
      {
        // ok, done
      }
      else
      {
        if(options.get_bool_option("pointer-check"))
        {
          std::string msg="memory model not applicable (got `";
          msg+=from_type(ns, "", result.value.type());
          msg+="', expected `";
          msg+=from_type(ns, "", dereference_type);
          msg+="')";

          dereference_callback.dereference_failure(
            "pointer dereference",
            msg, tmp_guard);
        }

        return valuet(); // give up, no way that this is ok
      }
    }
  }
  
  return result;
}

/*******************************************************************\

Function: dereferencet::valid_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dereferencet::valid_check(
  const exprt &object,
  const guardt &guard,
  const modet mode)
{
  if(!options.get_bool_option("pointer-check"))
    return;

  const exprt &symbol_expr=get_symbol(object);

  if(symbol_expr.id()==ID_string_constant)
  {
    // always valid, but can't write
    
    if(mode==WRITE)
    {
      dereference_callback.dereference_failure(
        "pointer dereference",
        "write access to string constant",
        guard);
    }
  }
  else if(symbol_expr.is_nil() ||
          symbol_expr.get_bool(ID_C_invalid_object))
  { 
    // always "valid", shut up
    return;
  }
  else if(symbol_expr.id()==ID_symbol)
  {
    const irep_idt identifier=
      to_symbol_expr(symbol_expr).get_identifier();
    
    const symbolt &symbol=ns.lookup(identifier);
    
    if(symbol.type.get_bool(ID_C_is_failed_symbol))
    {
      dereference_callback.dereference_failure(
        "pointer dereference",
        "invalid pointer",
        guard);
    }

    #if 0  
    if(dereference_callback.is_valid_object(identifier))
      return; // always ok
    #endif
  }
}

/*******************************************************************\

Function: dereferencet::bounds_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dereferencet::bounds_check(
  const index_exprt &expr,
  const guardt &guard)
{
  if(!options.get_bool_option("pointer-check"))
    return;

  if(!options.get_bool_option("bounds-check"))
    return;

  const typet &array_type=ns.follow(expr.op0().type());

  if(array_type.id()!=ID_array)
    throw "bounds check expected array type";

  std::string name=array_name(ns, expr.array());
  
  {
    mp_integer i;
    if(!to_integer(expr.index(), i) &&
       i>=0)
    {
    }
    else
    {
      exprt zero=gen_zero(expr.index().type());

      if(zero.is_nil())
        throw "no zero constant of index type "+
          expr.index().type().to_string();

      binary_relation_exprt
        inequality(expr.index(), ID_lt, zero);

      guardt tmp_guard(guard);
      tmp_guard.add(inequality);
      dereference_callback.dereference_failure(
        "array bounds",
        name+" lower bound", tmp_guard);
    }
  }

  const exprt &size_expr=
    to_array_type(array_type).size();
    
  if(size_expr.id()==ID_infinity)
  {
  }
  else if(size_expr.is_zero() && expr.array().id()==ID_member)
  {
    // this is a variable-sized struct field
  }
  else
  {
    if(size_expr.is_nil())
      throw "index array operand of wrong type";

    binary_relation_exprt inequality(expr.index(), ID_ge, size_expr);

    if(c_implicit_typecast(
      inequality.op0(),
      inequality.op1().type(),
      ns))
      throw "index address of wrong type";

    guardt tmp_guard(guard);
    tmp_guard.add(inequality);
    dereference_callback.dereference_failure(
      "array bounds",
      name+" upper bound", tmp_guard);
  }
}

/*******************************************************************\

Function: dereferencet::memory_model

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static unsigned bv_width(const typet &type)
{
  return atoi(type.get(ID_width).c_str());
}

static bool is_a_bv_type(const typet &type)
{
  return type.id()==ID_unsignedbv ||
         type.id()==ID_signedbv ||
         type.id()==ID_bv ||
         type.id()==ID_fixedbv ||
         type.id()==ID_floatbv;
}

bool dereferencet::memory_model(
  exprt &value,
  const typet &to_type,
  const guardt &guard,
  const exprt &offset)
{
  // we will allow more or less arbitrary pointer type cast

  const typet from_type=value.type();

  // first, check if it's really just a type coercion,
  // i.e., both have exactly the same (constant) size

  if(is_a_bv_type(from_type) &&
     is_a_bv_type(to_type))
  {
    if(bv_width(from_type)==bv_width(to_type))
      return memory_model_conversion(value, to_type, guard, offset);
  }

  // we are willing to do the same for pointers

  if(from_type.id()==ID_pointer &&
     to_type.id()==ID_pointer)
  {
    if(bv_width(from_type)==bv_width(to_type))
      return memory_model_conversion(value, to_type, guard, offset);
  }

  // otherwise, we will stich it together from bytes
  
  return memory_model_bytes(value, to_type, guard, offset);
}

/*******************************************************************\

Function: dereferencet::memory_model_conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dereferencet::memory_model_conversion(
  exprt &value,
  const typet &to_type,
  const guardt &guard,
  const exprt &offset)
{
  const typet from_type=value.type();

  // avoid semantic conversion in case of
  // cast to float or fixed-point
  if(from_type.id()!=ID_bv &&
     (to_type.id()==ID_fixedbv || to_type.id()==ID_floatbv))
  {
    value.make_typecast(bv_typet(bv_width(from_type)));
    value.make_typecast(to_type);
  }
  else
  {
    // only doing type conversion
    // just do the typecast
    value.make_typecast(to_type);
  }

  // also assert that offset is zero

  if(options.get_bool_option("pointer-check"))
  {
    equal_exprt offset_not_zero(offset, gen_zero(offset.type()));
    offset_not_zero.make_not();
  
    guardt tmp_guard(guard);
    tmp_guard.add(offset_not_zero);
    dereference_callback.dereference_failure(
      "word bounds",
      "offset not zero", tmp_guard);
  }

  return true;
}

/*******************************************************************\

Function: dereferencet::memory_model_bytes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dereferencet::memory_model_bytes(
  exprt &value,
  const typet &to_type,
  const guardt &guard,
  const exprt &offset)
{
  const typet from_type=value.type();
  
  // We simply refuse to convert to/from code.
  if(from_type.id()==ID_code || to_type.id()==ID_code)
    return false;

  // We won't do this without a committment to an endianness.
  if(config.ansi_c.endianness==configt::ansi_ct::NO_ENDIANNESS)
    return false; 

  // But everything else we will try!
  // We just rely on byte_extract to do the job!
  
  exprt result;

  // See if we have an array of bytes already,
  // and we want something byte-sized.
  if(ns.follow(from_type).id()==ID_array &&
     pointer_offset_size(ns, ns.follow(from_type).subtype())==1 &&
     pointer_offset_size(ns, to_type)==1 &&
     is_a_bv_type(ns.follow(from_type).subtype()) &&
     is_a_bv_type(to_type))
  {
    // yes, can use 'index'
    result=index_exprt(value, offset, ns.follow(from_type).subtype());
    
    // possibly need to convert
    if(!base_type_eq(result.type(), to_type, ns))
      result.make_typecast(to_type);
  }
  else
  {
    // no, use 'byte_extract'
    result=exprt(byte_extract_id(), to_type);
    result.copy_to_operands(value, offset);
  }
  
  value=result;

  // are we within the bounds?
  if(options.get_bool_option("pointer-check"))
  {
    // upper bound
    {
      mp_integer from_width=pointer_offset_size(ns, from_type);
      mp_integer to_width=pointer_offset_size(ns, to_type);
    
      exprt bound=from_integer(from_width-to_width, offset.type());

      binary_relation_exprt
        offset_upper_bound(offset, ID_gt, bound);
      
      guardt tmp_guard(guard);
      tmp_guard.add(offset_upper_bound);
      dereference_callback.dereference_failure(
        "pointer dereference",
        "object upper bound", tmp_guard);
    }

    // lower bound is easy
    if(!offset.is_zero())
    {
      binary_relation_exprt
        offset_lower_bound(offset, ID_lt,
                           gen_zero(offset.type()));

      guardt tmp_guard(guard);
      tmp_guard.add(offset_lower_bound);                
      dereference_callback.dereference_failure(
        "pointer dereference",
        "object lower bound", tmp_guard);
    }
  }

  return true;
}

#endif
