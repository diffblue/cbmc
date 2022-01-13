/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "value_set_dereference.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/json.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/range.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

#include <deque>

#include "dereference_callback.h"

/// Returns true if \p expr is complicated enough that a local definition (using
/// a let expression) is preferable to repeating it, potentially many times.
/// Of course this is just a heuristic -- currently we allow any expression that
/// only involves one symbol, such as "x", "(type*)x", "x[0]" (but not "x[y]").
/// Particularly we want to make sure to insist on a local definition of \p expr
/// is a large if-expression, such as `p == &o1 ? o1 : p == &o2 ? o2 : ...`, as
/// can result from dereferencing a subexpression (though note that \ref
/// value_set_dereferencet::dereference special-cases if_exprt, and therefore
/// handles the specific case of a double-dereference (**p) without an
/// intervening member operator, typecast, pointer arithmetic, etc.)
static bool should_use_local_definition_for(const exprt &expr)
{
  bool seen_symbol = false;
  for(auto it = expr.depth_begin(), itend = expr.depth_end(); it != itend; ++it)
  {
    if(it->id() == ID_symbol)
    {
      if(seen_symbol)
        return true;
      else
        seen_symbol = true;
    }
  }

  return false;
}

static json_objectt value_set_dereference_stats_to_json(
  const exprt &pointer,
  const std::vector<exprt> &points_to_set,
  const std::vector<exprt> &retained_values,
  const exprt &value)
{
  json_objectt json_result;
  json_result["Pointer"] = json_stringt{format_to_string(pointer)};
  json_result["PointsToSetSize"] =
    json_numbert{std::to_string(points_to_set.size())};

  json_arrayt points_to_set_json;
  for(const auto &object : points_to_set)
  {
    points_to_set_json.push_back(json_stringt{format_to_string(object)});
  }

  json_result["PointsToSet"] = points_to_set_json;

  json_result["RetainedValuesSetSize"] =
    json_numbert{std::to_string(points_to_set.size())};

  json_arrayt retained_values_set_json;
  for(auto &retained_value : retained_values)
  {
    retained_values_set_json.push_back(
      json_stringt{format_to_string(retained_value)});
  }

  json_result["RetainedValuesSet"] = retained_values_set_json;

  json_result["Value"] = json_stringt{format_to_string(value)};

  return json_result;
}

optionalt<exprt> value_set_dereferencet::try_add_offset_to_indices(
  const exprt &expr,
  const exprt &offset_elements)
{
  if(const auto *index_expr = expr_try_dynamic_cast<index_exprt>(expr))
  {
    return index_exprt{
      index_expr->array(),
      plus_exprt{index_expr->index(),
                 typecast_exprt::conditional_cast(
                   offset_elements, index_expr->index().type())}};
  }
  else if(const auto *if_expr = expr_try_dynamic_cast<if_exprt>(expr))
  {
    const auto true_case =
      try_add_offset_to_indices(if_expr->true_case(), offset_elements);
    if(!true_case)
      return {};
    const auto false_case =
      try_add_offset_to_indices(if_expr->false_case(), offset_elements);
    if(!false_case)
      return {};
    return if_exprt{if_expr->cond(), *true_case, *false_case};
  }
  else
  {
    return {};
  }
}

exprt value_set_dereferencet::dereference(
  const exprt &pointer,
  bool display_points_to_sets)
{
  if(pointer.type().id()!=ID_pointer)
    throw "dereference expected pointer type, but got "+
          pointer.type().pretty();

  // we may get ifs due to recursive calls
  if(pointer.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(pointer);
    exprt true_case = dereference(if_expr.true_case(), display_points_to_sets);
    exprt false_case =
      dereference(if_expr.false_case(), display_points_to_sets);
    return if_exprt(if_expr.cond(), true_case, false_case);
  }
  else if(pointer.id() == ID_typecast)
  {
    const exprt *underlying = &pointer;
    // Note this isn't quite the same as skip_typecast, which would also skip
    // things such as int-to-ptr typecasts which we shouldn't ignore
    while(underlying->id() == ID_typecast &&
          underlying->type().id() == ID_pointer)
    {
      underlying = &to_typecast_expr(*underlying).op();
    }

    if(underlying->id() == ID_if && underlying->type().id() == ID_pointer)
    {
      const auto &if_expr = to_if_expr(*underlying);
      return if_exprt(
        if_expr.cond(),
        dereference(
          typecast_exprt(if_expr.true_case(), pointer.type()),
          display_points_to_sets),
        dereference(
          typecast_exprt(if_expr.false_case(), pointer.type()),
          display_points_to_sets));
    }
  }
  else if(pointer.id() == ID_plus && pointer.operands().size() == 2)
  {
    // Try to improve results for *(p + i) where p points to known offsets but
    // i is non-constant-- if `p` points to known positions in arrays or array-members
    // of structs then we can add the non-constant expression `i` to the index
    // instead of using a byte-extract expression.

    exprt pointer_expr = to_plus_expr(pointer).op0();
    exprt offset_expr = to_plus_expr(pointer).op1();

    if(can_cast_type<pointer_typet>(offset_expr.type()))
      std::swap(pointer_expr, offset_expr);

    if(
      can_cast_type<pointer_typet>(pointer_expr.type()) &&
      !can_cast_type<pointer_typet>(offset_expr.type()) &&
      !can_cast_expr<constant_exprt>(offset_expr))
    {
      exprt derefd_pointer = dereference(pointer_expr);
      if(
        auto derefd_with_offset =
          try_add_offset_to_indices(derefd_pointer, offset_expr))
        return *derefd_with_offset;

      // If any of this fails, fall through to use the normal byte-extract path.
    }
  }

  return handle_dereference_base_case(pointer, display_points_to_sets);
}

exprt value_set_dereferencet::handle_dereference_base_case(
  const exprt &pointer,
  bool display_points_to_sets)
{ // type of the object
  const typet &type=pointer.type().subtype();

  // collect objects the pointer may point to
  const std::vector<exprt> points_to_set =
    dereference_callback.get_value_set(pointer);

  // get the values of these
  const std::vector<exprt> retained_values =
    make_range(points_to_set).filter([&](const exprt &value) {
      return !should_ignore_value(value, exclude_null_derefs, language_mode);
    });

  exprt compare_against_pointer = pointer;

  if(retained_values.size() >= 2 && should_use_local_definition_for(pointer))
  {
    symbolt fresh_binder = get_fresh_aux_symbol(
      pointer.type(),
      "derefd_pointer",
      "derefd_pointer",
      source_locationt(),
      language_mode,
      new_symbol_table);

    compare_against_pointer = fresh_binder.symbol_expr();
  }

  auto values =
    make_range(retained_values)
      .map([&](const exprt &value) {
        return build_reference_to(value, compare_against_pointer, ns);
      })
      .collect<std::deque<valuet>>();

  const bool may_fail =
    values.empty() ||
    std::any_of(values.begin(), values.end(), [](const valuet &value) {
      return value.value.is_nil();
    });

  if(may_fail)
  {
    values.push_front(get_failure_value(pointer, type));
  }

  // now build big case split, but we only do "good" objects

  exprt result_value = nil_exprt{};

  for(const auto &value : values)
  {
    if(value.value.is_not_nil())
    {
      if(result_value.is_nil()) // first?
        result_value = value.value;
      else
        result_value = if_exprt(value.pointer_guard, value.value, result_value);
    }
  }

  if(compare_against_pointer != pointer)
    result_value =
      let_exprt(to_symbol_expr(compare_against_pointer), pointer, result_value);

  if(display_points_to_sets)
  {
    log.status() << value_set_dereference_stats_to_json(
      pointer, points_to_set, retained_values, result_value);
  }

  return result_value;
}

value_set_dereferencet::valuet value_set_dereferencet::get_failure_value(
  const exprt &pointer,
  const typet &type)
{
  // first see if we have a "failed object" for this pointer
  exprt failure_value;

  if(
    const symbolt *failed_symbol =
      dereference_callback.get_or_create_failed_symbol(pointer))
  {
    // yes!
    failure_value = failed_symbol->symbol_expr();
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
    symbol.is_lvalue = true;

    failure_value = symbol.symbol_expr();
    failure_value.set(ID_C_invalid_object, true);
  }

  valuet result{};
  result.value = failure_value;
  result.pointer_guard = true_exprt();
  return result;
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
  const typet &dereference_type,
  const namespacet &ns)
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

  if(object_type == dereference_type)
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

/// Determine whether possible alias `what` should be ignored when replacing a
/// pointer by its referees.
/// We currently ignore a `null` object when \p exclude_null_derefs is true
/// (pass true if you know the dereferenced pointer cannot be null), and also
/// ignore integer addresses when \p language_mode is "java"
/// \param what: value set entry to convert to an expression: either
///   ID_unknown, ID_invalid, or an object_descriptor_exprt giving a referred
///   object and offset.
/// \param exclude_null_derefs: Ignore value-set entries that indicate a
///   given dereference may follow a null pointer
/// \param language_mode: Mode for any new symbols created to represent a
///   dereference failure
/// \return true if \p what should be ignored as a possible alias
bool value_set_dereferencet::should_ignore_value(
  const exprt &what,
  bool exclude_null_derefs,
  const irep_idt &language_mode)
{
  if(what.id() == ID_unknown || what.id() == ID_invalid)
  {
    return false;
  }

  const object_descriptor_exprt &o = to_object_descriptor_expr(what);

  const exprt &root_object = o.root_object();
  if(root_object.id() == ID_null_object)
  {
    return exclude_null_derefs;
  }
  else if(root_object.id() == ID_integer_address)
  {
    return language_mode == ID_java;
  }

  return false;
}

/// \param what: value set entry to convert to an expression: either
///   ID_unknown, ID_invalid, or an object_descriptor_exprt giving a referred
///   object and offset.
/// \param pointer_expr: pointer expression that may point to `what`
/// \param ns: A namespace
/// \return a `valuet` object containing `guard` and `value` fields.
///   The guard is an appropriate check to determine whether `pointer_expr`
///   really points to `what`; for example `pointer_expr == &what`.
///   The value corresponds to the dereferenced pointer_expr assuming it is
///   pointing to the object described by `what`.
///   For example, we might return
///   `{.value = global, .pointer_guard = (pointer_expr == &global)}`
value_set_dereferencet::valuet value_set_dereferencet::build_reference_to(
  const exprt &what,
  const exprt &pointer_expr,
  const namespacet &ns)
{
  const pointer_typet &pointer_type =
    type_checked_cast<pointer_typet>(pointer_expr.type());
  const typet &dereference_type = pointer_type.base_type();

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
    if(o.offset().is_zero())
      result.pointer = null_pointer_exprt{pointer_type};
    else
      return valuet{};
  }
  else if(root_object.id()==ID_dynamic_object)
  {
    // constraint that it actually is a dynamic object
    // this is also our guard
    result.pointer_guard = dynamic_object(pointer_expr);

    // can't remove here, turn into *p
    result.value = dereference_exprt{pointer_expr};
    result.pointer = pointer_expr;
  }
  else if(root_object.id()==ID_integer_address)
  {
    // This is stuff like *((char *)5).
    // This is turned into an access to __CPROVER_memory[...].

    const symbolt &memory_symbol=ns.lookup(CPROVER_PREFIX "memory");
    const symbol_exprt symbol_expr(memory_symbol.name, memory_symbol.type);

    if(memory_symbol.type.subtype() == dereference_type)
    {
      // Types match already, what a coincidence!
      // We can use an index expression.

      const index_exprt index_expr(
        symbol_expr,
        pointer_offset(pointer_expr),
        memory_symbol.type.subtype());

      result.value=index_expr;
      result.pointer = address_of_exprt{index_expr};
    }
    else if(
      dereference_type_compare(
        memory_symbol.type.subtype(), dereference_type, ns))
    {
      const index_exprt index_expr(
        symbol_expr,
        pointer_offset(pointer_expr),
        memory_symbol.type.subtype());
      result.value=typecast_exprt(index_expr, dereference_type);
      result.pointer =
        typecast_exprt{address_of_exprt{index_expr}, pointer_type};
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
        result.value = make_byte_extract(
          symbol_expr, pointer_offset(pointer_expr), dereference_type);
        result.pointer = address_of_exprt{result.value};
      }
    }
  }
  else
  {
    // something generic -- really has to be a symbol
    address_of_exprt object_pointer(object);

    if(o.offset().is_zero())
    {
      result.pointer_guard = equal_exprt(
        typecast_exprt::conditional_cast(pointer_expr, object_pointer.type()),
        object_pointer);
    }
    else
    {
      result.pointer_guard=same_object(pointer_expr, object_pointer);
    }

    const typet &object_type = object.type();
    const typet &root_object_type = root_object.type();

    exprt root_object_subexpression=root_object;

    if(
      dereference_type_compare(object_type, dereference_type, ns) &&
      o.offset().is_zero())
    {
      // The simplest case: types match, and offset is zero!
      // This is great, we are almost done.

      result.value = typecast_exprt::conditional_cast(object, dereference_type);
      result.pointer =
        typecast_exprt::conditional_cast(object_pointer, pointer_type);
    }
    else if(
      root_object_type.id() == ID_array &&
      dereference_type_compare(
        root_object_type.subtype(), dereference_type, ns))
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

      const index_exprt &index_expr =
        index_exprt(root_object, adjusted_offset, root_object_type.subtype());
      result.value =
        typecast_exprt::conditional_cast(index_expr, dereference_type);
      result.pointer = typecast_exprt::conditional_cast(
        address_of_exprt{index_expr}, pointer_type);
    }
    else
    {
      // try to build a member/index expression - do not use byte_extract
      auto subexpr = get_subexpression_at_offset(
        root_object_subexpression, o.offset(), dereference_type, ns);
      if(subexpr.has_value())
        simplify(subexpr.value(), ns);
      if(
        subexpr.has_value() &&
        subexpr.value().id() != ID_byte_extract_little_endian &&
        subexpr.value().id() != ID_byte_extract_big_endian)
      {
        // Successfully found a member, array index, or combination thereof
        // that matches the desired type and offset:
        result.value = subexpr.value();
        result.pointer = typecast_exprt::conditional_cast(
          address_of_exprt{skip_typecast(subexpr.value())}, pointer_type);
        return result;
      }

      // we extract something from the root object
      result.value=o.root_object();
      result.pointer = typecast_exprt::conditional_cast(
        address_of_exprt{skip_typecast(o.root_object())}, pointer_type);

      // this is relative to the root object
      exprt offset;
      if(o.offset().id()==ID_unknown)
        offset=pointer_offset(pointer_expr);
      else
        offset=o.offset();

      if(memory_model(result.value, dereference_type, offset, ns))
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
  const exprt &offset,
  const namespacet &ns)
{
  // we will allow more or less arbitrary pointer type cast

  const typet from_type=value.type();

  // first, check if it's really just a type coercion,
  // i.e., both have exactly the same (constant) size,
  // for bit-vector types or pointers

  if(
    (is_a_bv_type(from_type) && is_a_bv_type(to_type)) ||
    (from_type.id() == ID_pointer && to_type.id() == ID_pointer))
  {
    if(pointer_offset_bits(from_type, ns) == pointer_offset_bits(to_type, ns))
    {
      // avoid semantic conversion in case of
      // cast to float or fixed-point,
      // or cast from float or fixed-point

      if(
        to_type.id() != ID_fixedbv && to_type.id() != ID_floatbv &&
        from_type.id() != ID_fixedbv && from_type.id() != ID_floatbv)
      {
        value = typecast_exprt::conditional_cast(value, to_type);
        return true;
      }
    }
  }

  // otherwise, we will stitch it together from bytes

  return memory_model_bytes(value, to_type, offset, ns);
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
  const exprt &offset,
  const namespacet &ns)
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
  auto from_type_subtype_size = pointer_offset_size(from_type.subtype(), ns);

  auto to_type_size = pointer_offset_size(to_type, ns);

  if(
    from_type.id() == ID_array && from_type_subtype_size.has_value() &&
    *from_type_subtype_size == 1 && to_type_size.has_value() &&
    *to_type_size == 1 && is_a_bv_type(from_type.subtype()) &&
    is_a_bv_type(to_type))
  {
    // yes, can use 'index', but possibly need to convert
    result = typecast_exprt::conditional_cast(
      index_exprt(value, offset, from_type.subtype()), to_type);
  }
  else
  {
    // no, use 'byte_extract'
    result = make_byte_extract(value, offset, to_type);
  }

  value=result;

  return true;
}
