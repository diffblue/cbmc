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
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/format_type.h>
#include <util/fresh_symbol.h>
#include <util/options.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/range.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/ssa_expr.h>

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

/// Allocate a fresh derefd_pointer temporary variable
static symbol_exprt create_temporary_for(
  const exprt &pointer,
  irep_idt language_mode,
  symbol_tablet &symbol_table)
{
  return get_fresh_aux_symbol(
           pointer.type(),
           "derefd_pointer",
           "derefd_pointer",
           source_locationt(),
           language_mode,
           symbol_table)
    .symbol_expr();
}

typedef value_set_dereferencet::value_set_mappingt value_set_mappingt;
typedef value_set_dereferencet::value_set_resultt value_set_resultt;
typedef value_set_dereferencet::valuet valuet;

/// Returns true if the passed value-sets have any overlapping members, or if
/// more than one of them may result in a dereference failure.
static bool
value_sets_overlap(const std::vector<value_set_mappingt> &value_sets)
{
  PRECONDITION(!value_sets.empty());
  if(value_sets.size() == 1)
    return false;

  // If more than one value-set has the may-fail flag set then we consider that
  // they overlap:
  if(
    std::count_if(
      value_sets.begin(),
      value_sets.end(),
      [](const value_set_mappingt &value_set) {
        return value_set.values.may_fail;
      }) >= 2)
  {
    return true;
  }

  std::unordered_set<exprt, irep_hash> values_seen;
  for(const auto &value_set : value_sets)
    for(const auto &value : value_set.values.values)
      if(!values_seen.insert(value.value).second)
        return true;

  return false;
}

static value_set_resultt combine_value_sets(
  const std::vector<value_set_mappingt> &value_sets,
  const exprt &pointer)
{
  value_set_resultt result = {pointer,
                              {},
                              std::any_of(
                                value_sets.begin(),
                                value_sets.end(),
                                [](const value_set_mappingt &value_set) {
                                  return value_set.values.may_fail;
                                })};

  std::unordered_set<exprt, irep_hash> values_seen;
  std::vector<valuet> unchecked_values;

  for(const auto &value_set : value_sets)
  {
    for(const auto &value : value_set.values.values)
    {
      if(values_seen.insert(value.value).second)
      {
        if(value.pointer_guard.is_nil() || value.pointer_guard == true_exprt())
          unchecked_values.push_back(value);
        else
          result.values.push_back(value);
      }
    }
  }

  // value-set -> if-expression conversion currently relies on aliases without
  // a check appearing first in the list of possible aliases. If there are
  // several distinct such aliases then the result is unsound.
  result.values.insert(
    result.values.begin(), unchecked_values.begin(), unchecked_values.end());

  return result;
}

exprt value_set_dereferencet::dereference(const exprt &pointer)
{
  std::vector<value_set_mappingt> value_set_mappings;
  exprt derefd_pointer_with_placeholders =
    gather_value_sets(pointer, value_set_mappings);

  // derefd_pointer_with_placeholders is a copy of `pointer` with placeholder
  // symbols, e.g. "x ? placeholder1 : typecast(placeholder2, A*)"
  // (or in the simplest case just "placeholder1")
  // value_set_mappings maps each placeholder onto a set of values that
  // subexpression may point to.
  // We should now choose between two possible strategies:
  // 1. Keep the structure of derefd_pointer_with_placeholders and dereference
  //    each subexpression in place. We do this when the subexpressions'
  //    referents do not overlap; it doesn't require a temporary expresssion
  //    and produces a simpler result.
  // 2. Create a temporary for 'pointer' and handle the dereference as one
  //    large value-set. We do this when the referents overlap because it
  //    results in less redundancy.
  //
  // Example of case 1:
  // *(x ? y : z) ==>
  // *(x ? placeholder1 / {a,b} : placeholder2 / {c,d}) ==>
  // x ? (y == &a ? a : b) : (z == &c ? c : d)
  //
  // Introducing a temporary for (x ? y : z) would have had no benefit here.
  //
  // Example of case 2:
  // *(x ? y : z) ==>
  // *(x ? placeholder1 / {a,b,c} : placeholder2 / {a,b,c}) ==>
  // let derefd = (x ? y : z) in derefd == &a ? a : derefd == &b ? b : c
  //
  // Dereferencing y and z in-place would have led to a redundant construction
  // like (x ? (y == &a ? a : y == &b ? b : c) : (z == &a ? a ...
  // which leads to a larger formula, and in the case where goto-symex handles
  // such an if-expression on the LHS of an assignment, more write operations.

  if(!value_sets_overlap(value_set_mappings))
  {
    replace_symbolt replace_symbols;
    for(const auto &mapping : value_set_mappings)
    {
      replace_symbols.set(
        mapping.placeholder, value_set_to_conditional_expr(mapping.values));
    }
    replace_symbols(derefd_pointer_with_placeholders);
    return derefd_pointer_with_placeholders;
  }
  else
  {
    symbol_exprt pointer_temporary =
      create_temporary_for(pointer, language_mode, new_symbol_table);
    value_set_resultt combined_value_set =
      combine_value_sets(value_set_mappings, pointer_temporary);
    exprt result = value_set_to_conditional_expr(combined_value_set);
    return let_exprt(pointer_temporary, pointer, result);
  }
}

/// Produces a fresh placeholder variable name. We don't add these to the symbol
/// table, as they will be replaced before value_set_dereferencet::dereference
/// ends.
static symbol_exprt get_fresh_result_placeholder(const typet &type)
{
  static std::size_t i = 0;
  return symbol_exprt(
    "value_set_dereference::result_placeholder" + std::to_string(++i), type);
}

/// A placeholder value for the pointer being dereferenced. We only create one
/// of these as it is always replaced before
/// value_set_dereferencet::dereference ends.
static symbol_exprt get_pointer_placeholder(const typet &type)
{
  return symbol_exprt("value_set_dereference::pointer_placeholder", type);
}

exprt value_set_dereferencet::gather_value_sets(
  const exprt &pointer,
  std::vector<value_set_mappingt> &value_set_accumulator) const
{
  if(pointer.type().id() != ID_pointer)
  {
    throw "gather_value_sets expected pointer type, but got " +
      pointer.type().pretty();
  }

  // we may get ifs due to recursive calls
  if(pointer.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(pointer);
    exprt true_case =
      gather_value_sets(if_expr.true_case(), value_set_accumulator);
    exprt false_case =
      gather_value_sets(if_expr.false_case(), value_set_accumulator);
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
        gather_value_sets(
          typecast_exprt(if_expr.true_case(), pointer.type()),
          value_set_accumulator),
        gather_value_sets(
          typecast_exprt(if_expr.false_case(), pointer.type()),
          value_set_accumulator));
    }
  }

  // Create a fresh placeholder symbol, find this pointer's value-set, record
  // the placeholder -> value-set mapping, and return the new symbol:
  symbol_exprt result_placeholder =
    get_fresh_result_placeholder(to_pointer_type(pointer.type()).subtype());

  value_set_accumulator.emplace_back(
    value_set_mappingt{result_placeholder, get_value_set(pointer)});

  return value_set_accumulator.back().placeholder;
}

value_set_resultt
value_set_dereferencet::get_value_set(const exprt &pointer) const
{
#ifdef DEBUG
  std::cout << "value_set_dereferencet::get_value_set pointer="
            << format(pointer) << '\n';
#endif

  // collect objects the pointer may point to
  const std::vector<exprt> points_to_set =
    dereference_callback.get_value_set(pointer);

#ifdef DEBUG
  std::cout << "value_set_dereferencet::get_value_set points_to_set={";
  for(auto p : points_to_set)
    std::cout << format(p) << "; ";
  std::cout << "}\n" << std::flush;
#endif

  // get the values of these
  const std::vector<exprt> retained_values =
    make_range(points_to_set).filter([&](const exprt &value) {
      return !should_ignore_value(value, exclude_null_derefs, language_mode);
    });

#ifdef DEBUG
  std::cout << "value_set_dereferencet::get_value_set retained_values={";
  for(const auto &value : retained_values)
    std::cout << format(value) << "; ";
  std::cout << "}\n" << std::flush;
#endif

  // We use a placeholder symbol instead of the actual pointer when generating
  // value expressions because at this point we're unsure whether the values
  // will be output referring directly to `pointer` or to a parent expression.
  // For example, if `pointer` is `y` in the context `x ? y : z` then we might
  // end up outputting `y == &o1 ? o1 : ...` or we might go for
  // `tmp = x ? y : z; tmp == &o1 ? o1 : ...`. By using a standard placeholder
  // symbol we allow `value_set_dereferencet::dereference` to decide which
  // option to use. The placeholder will be replaced by the pointer expression
  // it selected in `value_set_to_conditional_expr`.
  symbol_exprt compare_against_pointer =
    get_pointer_placeholder(pointer.type());

  bool may_fail = false;
  std::vector<valuet> values =
    make_range(retained_values)
      .map([&](const exprt &value) {
        return build_reference_to(value, compare_against_pointer, ns);
      })
      .filter([&](const valuet &value) {
        if(value.value.is_nil())
          may_fail = true;
        return value.value.is_not_nil();
      });

  if(values.size() == 0)
    may_fail = true;

  return value_set_resultt{pointer, std::move(values), may_fail};
}

exprt value_set_dereferencet::value_set_to_conditional_expr(
  const value_set_resultt &value_set) const
{
  exprt result = nil_exprt();

  if(value_set.may_fail)
  {
    // Dereferencing this pointer may fail -- create a fallback option to
    // access some special symbol denoting an unknown or invalid object:

    // first see if we have a "failed object" for this pointer

    if(
      const symbolt *failed_symbol =
        dereference_callback.get_or_create_failed_symbol(value_set.pointer))
    {
      // yes!
      result = failed_symbol->symbol_expr();
      result.set(ID_C_invalid_object, true);
    }
    else
    {
      // else: produce new symbol
      symbolt &symbol = get_fresh_aux_symbol(
        to_pointer_type(value_set.pointer.type()).subtype(),
        "symex",
        "invalid_object",
        value_set.pointer.source_location(),
        language_mode,
        new_symbol_table);

      // make it a lvalue, so we can assign to it
      symbol.is_lvalue=true;

      result = symbol.symbol_expr();
      result.set(ID_C_invalid_object, true);
    }
  }

  std::size_t result_size = value_set.values.size();
  if(!result.is_nil())
    ++result_size;

  // now build big case split:

  for(const auto &value : value_set.values)
  {
    INVARIANT(
      value.value.is_not_nil(),
      "failed deref values should have been filtered already");

    if(result.is_nil()) // first?
      result = value.value;
    else
      result = if_exprt(value.pointer_guard, value.value, result);
  }

  // The expression built so far uses
  // value_set_dereferencet::pointer_placeholder in place of the actual
  // pointer. Choose whether to directly insert the pointer value, or if it is
  // complicated enough that we should declare a temporary to hold it:

  exprt compare_against_pointer;

  // We check for 3 values here because that is the smallest value-set size
  // that duplicates the pointer exprt (e.g. p == &a ? a : p == &b ? b : c)
  if(result_size >= 3 && should_use_local_definition_for(value_set.pointer))
  {
    compare_against_pointer =
      create_temporary_for(value_set.pointer, language_mode, new_symbol_table);
  }
  else
    compare_against_pointer = value_set.pointer;

  replace_symbolt replace_placeholder;
  replace_placeholder.set(
    get_pointer_placeholder(value_set.pointer.type()), compare_against_pointer);

  // Replace the pointer placeholder with its actual value:
  replace_placeholder(result);

  // Enclose in a let-expression if we used a temporary for the pointer:
  if(compare_against_pointer != value_set.pointer)
  {
    result = let_exprt(
      to_symbol_expr(compare_against_pointer), value_set.pointer, result);
  }

#ifdef DEBUG
  std::cout << "value_set_derefencet::value_set_to_conditional_expr result="
            << format(result) << '\n'
            << std::flush;
#endif

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
  const typet &dereference_type = pointer_type.subtype();

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
        result.value = byte_extract_exprt(
          byte_extract_id(),
          symbol_expr,
          pointer_offset(pointer_expr),
          dereference_type);
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
      if(subexpr.has_value() && subexpr.value().id() != byte_extract_id())
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
    result = byte_extract_exprt(byte_extract_id(), value, offset, to_type);
  }

  value=result;

  return true;
}
