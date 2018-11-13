/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "value_set_dereference.h"

#ifdef DEBUG
#include <iostream>
#include <util/format_expr.h>
#endif

#include <util/arith_tools.h>
#include <util/array_name.h>
#include <util/base_type.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/format_type.h>
#include <util/fresh_symbol.h>
#include <util/guard.h>
#include <util/options.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/ssa_expr.h>

/// \return The compound for a member expression, the array for an index
///   expression, `expr` otherwise.
const exprt &value_set_dereferencet::get_symbol(const exprt &expr)
{
  if(expr.id()==ID_member || expr.id()==ID_index)
    return get_symbol(expr.op0());

  return expr;
}

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
  std::cout << "DEREF: " << format(pointer) << '\n';
#endif

  // collect objects the pointer may point to
  value_setst::valuest points_to_set;

  dereference_callback.get_value_set(pointer, points_to_set);

#if 0
  for(value_setst::valuest::const_iterator
      it=points_to_set.begin();
      it!=points_to_set.end();
      it++)
    std::cout << "P: " << format(*it) << '\n';
#endif

  // get the values of these

  std::list<valuet> values;

  for(value_setst::valuest::const_iterator
      it=points_to_set.begin();
      it!=points_to_set.end();
      it++)
  {
    valuet value = build_reference_to(*it, pointer);

#if 0
    std::cout << "V: " << format(value.pointer_guard) << " --> ";
    std::cout << format(value.value);
    if(value.ignore)
      std::cout << " (ignored)";
    std::cout << '\n';
#endif

    if(!value.ignore)
      values.push_back(value);
  }

  // can this fail?
  bool may_fail;

  if(values.empty())
  {
    may_fail=true;
  }
  else
  {
    may_fail=false;
    for(std::list<valuet>::const_iterator
        it=values.begin();
        it!=values.end();
        it++)
      if(it->value.is_nil())
        may_fail=true;
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
      symbolt &symbol = get_fresh_aux_symbol(
        type,
        "symex",
        "invalid_object",
        pointer.source_location(),
        language_mode,
        new_symbol_table);

      // make it a lvalue, so we can assign to it
      symbol.is_lvalue=true;

      failure_value=symbol.symbol_expr();
      failure_value.set(ID_C_invalid_object, true);
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
  std::cout << "R: " << format(value) << "\n\n";
  #endif

  return value;
}

/// Check if the two types have matching number of ID_pointer levels, with
/// the dereference type eventually pointing to void; then this is ok
/// for example:
/// - dereference_type=void is ok (no matter what object_type is);
/// - object_type=(int *), dereference_type=(void *) is ok;
/// - object_type=(int **), dereference_type=(void **) is ok;
/// - object_type=(int **), dereference_type=(void *) is ok;
/// - object_type=(int *), dereference_type=(void **) is not ok;
bool value_set_dereferencet::dereference_type_compare(
  const typet &object_type,
  const typet &dereference_type) const
{
  const typet *object_unwrapped = &object_type;
  const typet *dereference_unwrapped = &dereference_type;
  while(object_unwrapped->id() == ID_pointer &&
        dereference_unwrapped->id() == ID_pointer)
  {
    object_unwrapped = &object_unwrapped->subtype();
    dereference_unwrapped = &dereference_unwrapped->subtype();
  }
  if(dereference_unwrapped->id() == ID_empty)
  {
    return true;
  }
  else if(dereference_unwrapped->id() == ID_pointer &&
          object_unwrapped->id() != ID_pointer)
  {
#ifdef DEBUG
    std::cout << "value_set_dereference: the dereference type has "
                 "too many ID_pointer levels"
              << std::endl;
    std::cout << " object_type: " << object_type.pretty() << std::endl;
    std::cout << " dereference_type: " << dereference_type.pretty()
              << std::endl;
#endif
  }

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

  // bitvectors of same width are ok
  if((dereference_type.id()==ID_signedbv ||
      dereference_type.id()==ID_unsignedbv) &&
     (object_type.id()==ID_signedbv ||
      object_type.id()==ID_unsignedbv) &&
     to_bitvector_type(dereference_type).get_width()==
     to_bitvector_type(object_type).get_width())
    return true;

  // really different

  return false;
}

/// \param what: value set entry to convert to an expression: either
///   ID_unknown, ID_invalid, or an object_descriptor_exprt giving a referred
///   object and offset.
/// \param pointer_expr: pointer expression that may point to `what`
/// \return a `valuet` object containing `guard`, `value` and `ignore` fields.
///   The `ignore` field is true for a `null` object when `exclude_null_derefs`
///   is true and integer addresses in java mode.
///   The guard is an appropriate check to determine whether `pointer_expr`
///   really points to `what`.
///   The value corresponds to the dereferenced pointer_expr assuming it is
///   pointing to the object described by `what`.
///   For example, we might return
///   `{.value = global, .pointer_guard = (pointer_expr == &global),
///     .ignore = false}`
value_set_dereferencet::valuet value_set_dereferencet::build_reference_to(
  const exprt &what,
  const exprt &pointer_expr)
{
  const typet &dereference_type=
    ns.follow(pointer_expr.type()).subtype();

  if(what.id()==ID_unknown ||
     what.id()==ID_invalid)
  {
    return valuet();
  }

  if(what.id()!=ID_object_descriptor)
    throw "unknown points-to: "+what.id_string();

  const object_descriptor_exprt &o=to_object_descriptor_expr(what);

  const exprt &root_object=o.root_object();
  const exprt &object=o.object();

  #if 0
  std::cout << "O: " << format(root_object) << '\n';
  #endif

  valuet result;

  if(root_object.id() == ID_null_object)
  {
    if(exclude_null_derefs)
    {
      result.ignore = true;
    }
  }
  else if(root_object.id()==ID_dynamic_object)
  {
    // const dynamic_object_exprt &dynamic_object=
    //  to_dynamic_object_expr(root_object);

    // the object produced by malloc
    exprt malloc_object=
      ns.lookup(CPROVER_PREFIX "malloc_object").symbol_expr();

    exprt is_malloc_object=same_object(pointer_expr, malloc_object);

    // constraint that it actually is a dynamic object
    // this is also our guard
    result.pointer_guard = dynamic_object(pointer_expr);

    // can't remove here, turn into *p
    result.value=dereference_exprt(pointer_expr, dereference_type);
  }
  else if(root_object.id()==ID_integer_address)
  {
    // This is stuff like *((char *)5).
    // This is turned into an access to __CPROVER_memory[...].

    if(language_mode == ID_java)
    {
      result.ignore = true;
      return result;
    }

    const symbolt &memory_symbol=ns.lookup(CPROVER_PREFIX "memory");
    const symbol_exprt symbol_expr(memory_symbol.name, memory_symbol.type);

    if(base_type_eq(
         ns.follow(memory_symbol.type).subtype(),
         dereference_type, ns))
    {
      // Types match already, what a coincidence!
      // We can use an index expression.

      const index_exprt index_expr(
        symbol_expr,
        pointer_offset(pointer_expr),
        ns.follow(memory_symbol.type).subtype());

      result.value=index_expr;
    }
    else if(dereference_type_compare(
              ns.follow(memory_symbol.type).subtype(),
              dereference_type))
    {
      const index_exprt index_expr(
        symbol_expr,
        pointer_offset(pointer_expr),
        ns.follow(memory_symbol.type).subtype());
      result.value=typecast_exprt(index_expr, dereference_type);
    }
    else
    {
      // We need to use byte_extract.
      // Won't do this without a commitment to an endianness.

      if(config.ansi_c.endianness==configt::ansi_ct::endiannesst::NO_ENDIANNESS)
      {
      }
      else
      {
        result.value = byte_extract_exprt(
          byte_extract_id(),
          symbol_expr,
          pointer_offset(pointer_expr),
          dereference_type);
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

    const typet &object_type=ns.follow(object.type());
    const typet &root_object_type=ns.follow(root_object.type());

    exprt root_object_subexpression=root_object;

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
            dereference_type_compare(
              root_object_type.subtype(),
              dereference_type))
    {
      // We have an array with a subtype that matches
      // the dereferencing type.
      // We will require well-alignedness!

      exprt offset;

      // this should work as the object is essentially the root object
      if(o.offset().is_constant())
        offset=o.offset();
      else
        offset=pointer_offset(pointer_expr);

      exprt adjusted_offset;

      // are we doing a byte?
      auto element_size = pointer_offset_size(root_object_type.subtype(), ns);

      if(!element_size.has_value() || *element_size == 0)
      {
        throw "unknown or invalid type size of:\n" +
          root_object_type.subtype().pretty();
      }
      else if(*element_size == 1)
      {
        // no need to adjust offset
        adjusted_offset = offset;
      }
      else
      {
        exprt element_size_expr = from_integer(*element_size, offset.type());

        adjusted_offset=binary_exprt(
          offset, ID_div, element_size_expr, offset.type());

        // TODO: need to assert well-alignedness
      }

      index_exprt index_expr=
        index_exprt(root_object, adjusted_offset, root_object_type.subtype());

      result.value=index_expr;

      if(ns.follow(result.value.type())!=ns.follow(dereference_type))
        result.value.make_typecast(dereference_type);
    }
    else
    {
      // try to build a member/index expression - do not use byte_extract
      exprt subexpr = get_subexpression_at_offset(
        root_object_subexpression, o.offset(), dereference_type, ns);
      if(subexpr.is_not_nil())
        simplify(subexpr, ns);
      if(subexpr.is_not_nil() && subexpr.id() != byte_extract_id())
      {
        // Successfully found a member, array index, or combination thereof
        // that matches the desired type and offset:
        result.value = subexpr;
        return result;
      }

      // we extract something from the root object
      result.value=o.root_object();

      // this is relative to the root object
      exprt offset;
      if(o.offset().id()==ID_unknown)
        offset=pointer_offset(pointer_expr);
      else
        offset=o.offset();

      if(memory_model(result.value, dereference_type, offset))
      {
        // ok, done
      }
      else
      {
        return valuet(); // give up, no way that this is ok
      }
    }
  }

  return result;
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

/// Replace `value` by an expression of type `to_type` corresponding to the
/// value at memory address `value + offset`.
///
/// If `value` is a bitvector or pointer of the same size as `to_type`,
/// make `value` into the typecast expression `(to_type)value`.
/// Otherwise perform the same operation as
/// value_set_dereferencet::memory_model_bytes
/// \return true on success
bool value_set_dereferencet::memory_model(
  exprt &value,
  const typet &to_type,
  const exprt &offset)
{
  // we will allow more or less arbitrary pointer type cast

  const typet from_type=value.type();

  // first, check if it's really just a type coercion,
  // i.e., both have exactly the same (constant) size

  if(is_a_bv_type(from_type) &&
     is_a_bv_type(to_type))
  {
    if(pointer_offset_bits(from_type, ns) == pointer_offset_bits(to_type, ns))
    {
      // avoid semantic conversion in case of
      // cast to float or fixed-point,
      // or cast from float or fixed-point

      if(to_type.id()==ID_fixedbv || to_type.id()==ID_floatbv ||
         from_type.id()==ID_fixedbv || from_type.id()==ID_floatbv)
      {
      }
      else
        return memory_model_conversion(value, to_type);
    }
  }

  // we are willing to do the same for pointers

  if(from_type.id()==ID_pointer &&
     to_type.id()==ID_pointer)
  {
    if(pointer_offset_bits(from_type, ns) == pointer_offset_bits(to_type, ns))
      return memory_model_conversion(value, to_type);
  }

  // otherwise, we will stitch it together from bytes

  return memory_model_bytes(value, to_type, offset);
}

/// Make `value` into a typecast expression: `(to_type)value`
/// \return true
bool value_set_dereferencet::memory_model_conversion(
  exprt &value,
  const typet &to_type)
{
  // only doing type conversion
  // just do the typecast
  value.make_typecast(to_type);
  return true;
}

/// Replace `value` by an expression of type `to_type` corresponding to the
/// value at memory address `value + offset`.
///
/// If the type of value is an array of bitvectors of size 1 byte, and `to_type`
/// also is bitvector of size 1 byte, then the resulting expression is
/// `value[offset]` or `(to_type)value[offset]` when typecast is required.
/// Otherwise the expression is `byte_extract(value, offset)`.
/// \return false if the conversion cannot be made
bool value_set_dereferencet::memory_model_bytes(
  exprt &value,
  const typet &to_type,
  const exprt &offset)
{
  const typet from_type=value.type();

  // We simply refuse to convert to/from code.
  if(from_type.id()==ID_code || to_type.id()==ID_code)
    return false;

  // We won't do this without a commitment to an endianness.
  if(config.ansi_c.endianness==configt::ansi_ct::endiannesst::NO_ENDIANNESS)
    return false;

  // But everything else we will try!
  // We just rely on byte_extract to do the job!

  exprt result;

  // See if we have an array of bytes already,
  // and we want something byte-sized.
  auto from_type_subtype_size =
    pointer_offset_size(ns.follow(from_type).subtype(), ns);

  auto to_type_size = pointer_offset_size(to_type, ns);

  if(
    ns.follow(from_type).id() == ID_array &&
    from_type_subtype_size.has_value() && *from_type_subtype_size == 1 &&
    to_type_size.has_value() && *to_type_size == 1 &&
    is_a_bv_type(ns.follow(from_type).subtype()) && is_a_bv_type(to_type))
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
    result = byte_extract_exprt(byte_extract_id(), value, offset, to_type);
  }

  value=result;

  return true;
}
