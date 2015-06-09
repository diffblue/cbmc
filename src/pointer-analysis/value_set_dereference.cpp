/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <cassert>

#include <util/string2int.h>
#include <util/expr_util.h>
#include <util/c_misc.h>
#include <util/base_type.h>
#include <util/arith_tools.h>
#include <util/rename.h>
#include <util/i2string.h>
#include <util/array_name.h>
#include <util/config.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/pointer_offset_size.h>
#include <util/symbol_table.h>
#include <util/guard.h>
#include <util/options.h>
#include <util/pointer_predicates.h>
#include <util/byte_operators.h>

#include <ansi-c/c_types.h>
#include <ansi-c/c_typecast.h>

#include <pointer-analysis/value_set.h>

#include <langapi/language_util.h>

#include "value_set_dereference.h"
#include "pointer_offset_sum.h"

// global data, horrible
unsigned int value_set_dereferencet::invalid_counter=0;

/*******************************************************************\

Function: value_set_dereferencet::has_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_dereferencet::has_dereference(const exprt &expr)
{
  forall_operands(it, expr)
    if(has_dereference(*it))
      return true;

  if(expr.id()==ID_dereference)
    return true;

  // we no longer do this one
  if(expr.id()==ID_index &&
     expr.operands().size()==2 &&
     expr.op0().type().id()==ID_pointer)
    assert(false);  

  return false;
}

/*******************************************************************\

Function: value_set_dereferencet::get_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt &value_set_dereferencet::get_symbol(const exprt &expr)
{
  if(expr.id()==ID_member || expr.id()==ID_index)
    return get_symbol(expr.op0());
  
  return expr;
}

/*******************************************************************\

Function: value_set_dereferencet::dereference

  Inputs: expression dest, to be dereferenced under given guard,
          and given mode

 Outputs: returns pointer after dereferencing

 Purpose:

\*******************************************************************/

exprt value_set_dereferencet::dereference(
  const exprt &pointer,
  const guardt &guard,
  const modet mode)
{
  if(pointer.type().id()!=ID_pointer)
    throw "dereference expected pointer type, but got "+
          pointer.type().pretty();  

  // we may get ifs due to recursive calls
  if(pointer.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(pointer);
    // push down the if
    guardt true_guard=guard;
    guardt false_guard=guard;
    
    true_guard.add(if_expr.cond());
    false_guard.add(not_exprt(if_expr.cond()));
    
    exprt true_case=dereference(if_expr.true_case(), true_guard, mode);
    exprt false_case=dereference(if_expr.false_case(), false_guard, mode);
    
    return if_exprt(if_expr.cond(), true_case, false_case);
  }
  
  // type of the object
  const typet &type=pointer.type().subtype();

  #if 0
  std::cout << "DEREF: " << from_expr(ns, "", pointer) << std::endl;
  #endif

  // collect objects the pointer may point to
  value_setst::valuest points_to_set;
  
  dereference_callback.get_value_set(pointer, points_to_set);
  
  #if 0
  for(value_setst::valuest::const_iterator
      it=points_to_set.begin();
      it!=points_to_set.end();
      it++)
    std::cout << "P: " << from_expr(ns, "", *it) << std::endl;
  #endif

  // get the values of these

  std::list<valuet> values;

  for(value_setst::valuest::const_iterator
      it=points_to_set.begin();
      it!=points_to_set.end();
      it++)
  {
    valuet value=build_reference_to(*it, mode, pointer, guard);
    
    #if 0
    std::cout << "V: " << from_expr(ns, "", value.pointer_guard) << " --> ";
    std::cout << from_expr(ns, "", value.value) << std::endl;
    #endif

    values.push_back(value);
  }

  // can this fail?
  bool may_fail;
  
  if(values.empty())
  {
    invalid_pointer(pointer, guard);
    may_fail=true;
  }
  else
  {
    may_fail=false;
    for(std::list<valuet>::const_iterator
        it=values.begin();
        it!=values.end();
        it++)
      if(it->value.is_nil()) may_fail=true;
  }
  
  if(may_fail)
  {
    // first see if we have a "failed object" for this pointer
    
    const symbolt *failed_symbol;
    exprt failure_value;

    if(dereference_callback.has_failed_symbol(
         pointer, failed_symbol))
    {
      // yes!
      failure_value=failed_symbol->symbol_expr();
      failure_value.set(ID_C_invalid_object, true);
    }
    else
    {
      // else: produce new symbol

      symbolt symbol;
      symbol.name="symex::invalid_object"+i2string(invalid_counter++);
      symbol.base_name="invalid_object";
      symbol.type=type;

      // make it a lvalue, so we can assign to it
      symbol.is_lvalue=true;
      
      get_new_name(symbol, ns);

      failure_value=symbol.symbol_expr();
      failure_value.set(ID_C_invalid_object, true);
      
      new_symbol_table.move(symbol);
    }

    valuet value;
    value.value=failure_value;
    value.pointer_guard=true_exprt();
    values.push_front(value);
  }
  
  // now build big case split, but we only do "good" objects
  
  exprt value=nil_exprt();

  for(std::list<valuet>::const_iterator
      it=values.begin();
      it!=values.end();
      it++)
  {
    if(it->value.is_not_nil())
    {
      if(value.is_nil()) // first?
        value=it->value;
      else
        value=if_exprt(it->pointer_guard, it->value, value);
    }
  }
  
  #if 0
  std::cout << "R: " << from_expr(ns, "", value) << std::endl
            << std::endl;
  #endif

  return value;
}

/*******************************************************************\

Function: value_set_dereferencet::dereference_type_compare

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_dereferencet::dereference_type_compare(
  const typet &object_type,
  const typet &dereference_type) const
{
  if(dereference_type.id()==ID_empty)
    return true; // always ok

  if(base_type_eq(object_type, dereference_type, ns))
    return true; // ok, they just match

  // check for struct prefixes

  const typet ot_base=ns.follow(object_type),
              dt_base=ns.follow(dereference_type);

  if(ot_base.id()==ID_struct &&
     dt_base.id()==ID_struct)
  {
    if(to_struct_type(dt_base).is_prefix_of(
         to_struct_type(ot_base)))
      return true; // ok, dt is a prefix of ot
  }
  
  // we are generous about code pointers
  if(dereference_type.id()==ID_code &&
     object_type.id()==ID_code)
    return true;

  // really different

  return false;
}

/*******************************************************************\

Function: value_set_dereferencet::invalid_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_dereferencet::invalid_pointer(
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

Function: value_set_dereferencet::build_reference_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

value_set_dereferencet::valuet value_set_dereferencet::build_reference_to(
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
        pointer_offset_size(dereference_type, ns);
          
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

Function: value_set_dereferencet::valid_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_dereferencet::valid_check(
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

Function: value_set_dereferencet::bounds_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_dereferencet::bounds_check(
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

Function: value_set_dereferencet::memory_model

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static unsigned bv_width(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_c_enum_tag)
  {
    const typet &t=ns.follow_tag(to_c_enum_tag_type(type));
    assert(t.id()==ID_c_enum);
    return bv_width(t.subtype(), ns);
  }

  return unsafe_string2unsigned(type.get_string(ID_width));
}

static bool is_a_bv_type(const typet &type)
{
  return type.id()==ID_unsignedbv ||
         type.id()==ID_signedbv ||
         type.id()==ID_bv ||
         type.id()==ID_fixedbv ||
         type.id()==ID_floatbv ||
         type.id()==ID_c_enum_tag;
}

bool value_set_dereferencet::memory_model(
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
    if(bv_width(from_type, ns)==bv_width(to_type, ns))
    {
      // avoid semantic conversion in case of
      // cast to float or fixed-point,
      // or cast from float or fixed-point

      if(to_type.id()==ID_fixedbv || to_type.id()==ID_floatbv ||
         from_type.id()==ID_fixedbv || from_type.id()==ID_floatbv)
      {
      }
      else
        return memory_model_conversion(value, to_type, guard, offset);
    }
  }

  // we are willing to do the same for pointers

  if(from_type.id()==ID_pointer &&
     to_type.id()==ID_pointer)
  {
    if(bv_width(from_type, ns)==bv_width(to_type, ns))
      return memory_model_conversion(value, to_type, guard, offset);
  }

  // otherwise, we will stich it together from bytes
  
  return memory_model_bytes(value, to_type, guard, offset);
}

/*******************************************************************\

Function: value_set_dereferencet::memory_model_conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_dereferencet::memory_model_conversion(
  exprt &value,
  const typet &to_type,
  const guardt &guard,
  const exprt &offset)
{
  // only doing type conversion
  // just do the typecast
  value.make_typecast(to_type);

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

Function: value_set_dereferencet::memory_model_bytes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_dereferencet::memory_model_bytes(
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
     pointer_offset_size(ns.follow(from_type).subtype(), ns)==1 &&
     pointer_offset_size(to_type, ns)==1 &&
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
      mp_integer from_width=pointer_offset_size(from_type, ns);
      mp_integer to_width=pointer_offset_size(to_type, ns);
    
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

