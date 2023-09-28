/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation Utilities

#include "shadow_memory_util.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/ssa_expr.h>
#include <util/std_expr.h>


// TODO: change DEBUG_SM to DEBUG_SHADOW_MEMORY (it also appears in other files)

irep_idt extract_field_name(const exprt &string_expr)
{
  if(can_cast_expr<typecast_exprt>(string_expr))
    return extract_field_name(to_typecast_expr(string_expr).op());
  else if(can_cast_expr<address_of_exprt>(string_expr))
    return extract_field_name(to_address_of_expr(string_expr).object());
  else if(can_cast_expr<index_exprt>(string_expr))
    return extract_field_name(to_index_expr(string_expr).array());
  else if(string_expr.id() == ID_string_constant)
  {
    return string_expr.get(ID_value);
  }
  else
    UNREACHABLE;
}

/// If the given type is an array type, then remove the L2 level renaming
/// from its size.
/// \param type Type to be modified
static void remove_array_type_l2(typet &type)
{
  if(to_array_type(type).size().id() != ID_symbol)
    return;

  ssa_exprt &size = to_ssa_expr(to_array_type(type).size());
  size.remove_level_2();
}

exprt deref_expr(const exprt &expr)
{
  if(can_cast_expr<address_of_exprt>(expr))
  {
    return to_address_of_expr(expr).object();
  }

  return dereference_exprt(expr);
}

void clean_pointer_expr(exprt &expr, const typet &type)
{
  if(
    can_cast_type<array_typet>(type) && can_cast_expr<symbol_exprt>(expr) &&
    to_array_type(type).size().get_bool(ID_C_SSA_symbol))
  {
    remove_array_type_l2(expr.type());
    exprt original_expr = to_ssa_expr(expr).get_original_expr();
    remove_array_type_l2(original_expr.type());
    to_ssa_expr(expr).set_expression(original_expr);
  }
  if(expr.id() == ID_string_constant)
  {
    expr = address_of_exprt(expr);
    expr.type() = pointer_type(char_type());
  }
  else if(can_cast_expr<dereference_exprt>(expr))
  {
    expr = to_dereference_expr(expr).pointer();
  }
  else
  {
    expr = address_of_exprt(expr);
  }
  POSTCONDITION(can_cast_type<pointer_typet>(expr.type()));
}

void log_set_field(
  const namespacet &ns,
  const messaget &log,
  const irep_idt &field_name,
  const exprt &expr,
  const exprt &value)
{
  log.conditional_output(
    log.debug(), [field_name, ns, expr, value](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: set_field: " << id2string(field_name)
              << " for " << format(expr) << " to " << format(value)
              << messaget::eom;
    });
}

void log_get_field(
  const namespacet &ns,
  const messaget &log,
  const irep_idt &field_name,
  const exprt &expr)
{
  log.conditional_output(
    log.debug(), [ns, field_name, expr](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: get_field: " << id2string(field_name)
              << " for " << format(expr) << messaget::eom;
    });
}

void log_value_set(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, value_set](messaget::mstreamt &mstream) {
      for(const auto &e : value_set)
      {
        mstream << "Shadow memory: value_set: " << format(e) << messaget::eom;
      }
    });
#endif
}

void log_value_set_match(
  const namespacet &ns,
  const messaget &log,
  const shadow_memory_statet::shadowed_addresst &shadowed_address,
  const exprt &matched_base_address,
  const value_set_dereferencet::valuet &dereference,
  const exprt &expr,
  const value_set_dereferencet::valuet &shadow_dereference)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(),
    [ns,
     shadowed_address,
     expr,
     dereference,
     matched_base_address,
     shadow_dereference](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: value_set_match: " << messaget::eom;
      mstream << "Shadow memory:   base: " << format(shadowed_address.address)
              << " <-- " << format(matched_base_address) << messaget::eom;
      mstream << "Shadow memory:   cell: " << format(dereference.pointer)
              << " <-- " << format(expr) << messaget::eom;
      mstream << "Shadow memory:   shadow_ptr: "
              << format(shadow_dereference.pointer) << messaget::eom;
      mstream << "Shadow memory:   shadow_val: "
              << format(shadow_dereference.value) << messaget::eom;
    });
#endif
}

void log_value_set_match(
  const namespacet &ns,
  const messaget &log,
  const exprt &address,
  const exprt &expr)
{
  // Leave guards rename to DEBUG_SHADOW_MEMORY
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, address, expr](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: value_set_match: " << format(address)
              << " <-- " << format(expr) << messaget::eom;
    });
#endif
}

void log_try_shadow_address(
  const namespacet &ns,
  const messaget &log,
  const shadow_memory_statet::shadowed_addresst &shadowed_address)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, shadowed_address](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: trying shadowed address: "
              << format(shadowed_address.address) << messaget::eom;
    });
#endif
}

void log_cond(
  const namespacet &ns,
  const messaget &log,
  const char *cond_text,
  const exprt &cond)
{
#ifdef DEBUG_SM
  log.conditional_output(
    log.debug(), [ns, cond_text, cond](messaget::mstreamt &mstream) {
      mstream << "Shadow memory: " << cond_text << ": " << format(cond)
              << messaget::eom;
    });
#endif
}

static void log_are_types_incompatible(
  const namespacet &ns,
  const exprt &expr,
  const shadow_memory_statet::shadowed_addresst &shadowed_address,
  const messaget &log)
{
#ifdef DEBUG_SM
  log.debug() << "Shadow memory: incompatible types "
              << from_type(ns, "", expr.type()) << ", "
              << from_type(ns, "", shadowed_address.address.type())
              << messaget::eom;
#endif
}

void replace_invalid_object_by_null(exprt &expr)
{
  if(
    expr.id() == ID_symbol && expr.type().id() == ID_pointer &&
    (id2string(to_symbol_expr(expr).get_identifier()).rfind("invalid_object") !=
       std::string::npos ||
     id2string(to_symbol_expr(expr).get_identifier()).rfind("$object") !=
       std::string::npos))
  {
    expr = null_pointer_exprt(to_pointer_type(expr.type()));
    return;
  }
  Forall_operands(it, expr)
  {
    replace_invalid_object_by_null(*it);
  }
}

const exprt &
get_field_init_expr(const irep_idt &field_name, const goto_symex_statet &state)
{
  auto field_type_it = state.shadow_memory.fields.local_fields.find(field_name);
  if(field_type_it != state.shadow_memory.fields.local_fields.end())
  {
    return field_type_it->second;
  }
  field_type_it = state.shadow_memory.fields.global_fields.find(field_name);
  CHECK_RETURN(field_type_it != state.shadow_memory.fields.global_fields.end());
  return field_type_it->second;
}

const typet &
get_field_init_type(const irep_idt &field_name, const goto_symex_statet &state)
{
  const exprt &field_init_expr = get_field_init_expr(field_name, state);
  return field_init_expr.type();
}

bool contains_null_or_invalid(
  const std::vector<exprt> &value_set,
  const exprt &address)
{
  if(
    address.id() == ID_constant && address.type().id() == ID_pointer &&
    to_constant_expr(address).is_zero())
  {
    for(const auto &e : value_set)
    {
      if(e.id() != ID_object_descriptor)
        continue;

      const exprt &expr = to_object_descriptor_expr(e).object();
      if(expr.id() == ID_null_object)
        return true;
    }
    return false;
  }

  for(const auto &e : value_set)
  {
    if(e.id() == ID_unknown || e.id() == ID_object_descriptor)
      return true;
  }
  return false;
}

// TODO: doxygen?
static exprt conditional_cast_floatbv_to_unsignedbv(const exprt &value)
{
  if(value.type().id() != ID_floatbv)
  {
    return value;
  }
  return make_byte_extract(
    value,
    from_integer(0, unsigned_int_type()),
    unsignedbv_typet(to_bitvector_type(value.type()).get_width()));
}

// TODO: doxygen?
static void or_over_bytes(
  const exprt &value,
  const typet &type,
  const typet &field_type,
  exprt::operandst &values)
{
  const size_t size = to_bitvector_type(type).get_width() / 8;
  values.push_back(typecast_exprt::conditional_cast(value, field_type));
  for(size_t i = 1; i < size; ++i)
  {
    values.push_back(typecast_exprt::conditional_cast(
      lshr_exprt(value, from_integer(8 * i, size_type())), field_type));
  }
}

// TODO: doxygen?
static void or_elements(
  exprt element,
  const typet &field_type,
  const namespacet &ns,
  const messaget &log,
  const bool is_union,
  exprt::operandst &values)
{
  element = conditional_cast_floatbv_to_unsignedbv(element);
  if(element.type().id() == ID_unsignedbv || element.type().id() == ID_signedbv)
  {
    exprt value = element;
    if(is_union)
    {
      or_over_bytes(value, element.type(), field_type, values);
    }
    else
    {
      values.push_back(typecast_exprt::conditional_cast(value, field_type));
    }
  }
  else
  {
    exprt value = compute_or_over_cells(element, field_type, ns, log, is_union);
    values.push_back(typecast_exprt::conditional_cast(value, field_type));
  }
}

/// Translate a list of values into an or expression. Used here in the implementation
/// of aggregation of boolean-typed fields.
/// \param field_type The type of the values of the or expression (expected to be
///    the same).
/// \param values A list (std::vector) of values collected previously, passed
///    through immediatelly to the constructed expression as operands.
/// \return A newly constructed or_exprt over the possible values given.
static exprt or_values(const exprt::operandst &values, const typet &field_type)
{
  if(values.size() == 1)
  {
    return values[0];
  }
  // TODO: FOTIS: Just `or_exprt`?
  return multi_ary_exprt(ID_bitor, values, field_type);
}

exprt compute_or_over_cells(
  const exprt &expr,
  const typet &field_type,
  const namespacet &ns,
  const messaget &log,
  const bool is_union)
{
  const typet type = ns.follow(expr.type());

  if(type.id() == ID_struct || type.id() == ID_union)
  {
    exprt::operandst values;
    for(const auto &component : to_struct_union_type(type).components())
    {
      if(component.get_is_padding())
      {
        continue;
      }
      or_elements(
        member_exprt(expr, component), field_type, ns, log, is_union, values);
    }
    return or_values(values, field_type);
  }
  else if(type.id() == ID_array)
  {
    const array_typet &array_type = to_array_type(type);
    if(array_type.size().is_constant())
    {
      exprt::operandst values;
      const mp_integer size =
        numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));
      for(mp_integer index = 0; index < size; ++index)
      {
        or_elements(
          index_exprt(expr, from_integer(index, index_type())),
          field_type,
          ns,
          log,
          is_union,
          values);
      }
      return or_values(values, field_type);
    }
    else
    {
      log.warning()
        << "Shadow memory: cannot compute or over variable-size array "
        << format(expr) << messaget::eom;
    }
  }
  exprt::operandst values;
  if(is_union)
  {
    or_over_bytes(
      conditional_cast_floatbv_to_unsignedbv(expr), type, field_type, values);
  }
  else
  {
    values.push_back(typecast_exprt::conditional_cast(
      conditional_cast_floatbv_to_unsignedbv(expr), field_type));
  }
  return or_values(values, field_type);
}

// TODO: doxygen?
static void
max_element(const exprt &element, const typet &field_type, exprt &max)
{
  exprt value = typecast_exprt::conditional_cast(element, field_type);
  if(max.is_nil())
  {
    max = value;
  }
  else
  {
    max = if_exprt(binary_predicate_exprt(value, ID_gt, max), value, max);
  }
}

// TODO: doxygen?
static void max_over_bytes(
  const exprt &value,
  const typet &type,
  const typet &field_type,
  exprt &max)
{
  const size_t size = to_bitvector_type(type).get_width() / 8;
  max_element(value, field_type, max);
  for(size_t i = 1; i < size; ++i)
  {
    max_element(
      lshr_exprt(value, from_integer(8 * i, size_type())), field_type, max);
  }
}

// TODO: doxygen?
static void max_elements(
  exprt element,
  const typet &field_type,
  const namespacet &ns,
  const messaget &log,
  const bool is_union,
  exprt &max)
{
  element = conditional_cast_floatbv_to_unsignedbv(element);
  if(element.type().id() == ID_unsignedbv || element.type().id() == ID_signedbv)
  {
    if(is_union)
    {
      max_over_bytes(element, element.type(), field_type, max);
    }
    else
    {
      max_element(element, field_type, max);
    }
  }
  else
  {
    exprt value =
      compute_max_over_cells(element, field_type, ns, log, is_union);
    max_element(value, field_type, max);
  }
}

exprt compute_max_over_cells(
  const exprt &expr,
  const typet &field_type,
  const namespacet &ns,
  const messaget &log,
  const bool is_union)
{
  const typet type = ns.follow(expr.type());

  if(type.id() == ID_struct || type.id() == ID_union)
  {
    exprt max = nil_exprt();
    for(const auto &component : to_struct_union_type(type).components())
    {
      if(component.get_is_padding())
      {
        continue;
      }
      max_elements(
        member_exprt(expr, component), field_type, ns, log, is_union, max);
    }
    return max;
  }
  else if(type.id() == ID_array)
  {
    const array_typet &array_type = to_array_type(type);
    if(array_type.size().is_constant())
    {
      exprt max = nil_exprt();
      const mp_integer size =
        numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));
      for(mp_integer index = 0; index < size; ++index)
      {
        max_elements(
          index_exprt(expr, from_integer(index, index_type())),
          field_type,
          ns,
          log,
          is_union,
          max);
      }
      return max;
    }
    else
    {
      log.warning()
        << "Shadow memory: cannot compute max over variable-size array "
        << format(expr) << messaget::eom;
    }
  }
  // TODO: This is incorrect when accessing non-0 offsets of scalars.
  return typecast_exprt::conditional_cast(
    conditional_cast_floatbv_to_unsignedbv(expr), field_type);
}

// TODO: doxygen?
exprt build_if_else_expr(
  const std::vector<std::pair<exprt, exprt>> &conds_values)
{
  DATA_INVARIANT(
    !conds_values.empty(), "build_if_else_expr requires non-empty argument");
  exprt result = nil_exprt();
  for(const auto &cond_value : conds_values)
  {
    if(result.is_nil())
    {
      result = cond_value.second;
    }
    else
    {
      result = if_exprt(cond_value.first, cond_value.second, result);
    }
  }
  return result;
}

// TODO: doxygen?
static bool
are_types_compatible(const typet &expr_type, const typet &shadow_type)
{
  if(expr_type.id() != ID_pointer || shadow_type.id() != ID_pointer)
    return true;

  // We filter out the particularly annoying case of char ** being definitely
  // incompatible with char[].
  const typet &expr_subtype = to_pointer_type(expr_type).base_type();
  const typet &shadow_subtype = to_pointer_type(shadow_type).base_type();

  if(
    expr_subtype.id() == ID_pointer &&
    to_pointer_type(expr_subtype).base_type().id() != ID_pointer &&
    shadow_subtype.id() == ID_array &&
    to_array_type(shadow_subtype).element_type().id() != ID_pointer)
  {
    return false;
  }
  if(
    shadow_subtype.id() == ID_pointer &&
    to_pointer_type(shadow_subtype).base_type().id() != ID_pointer &&
    expr_subtype.id() != ID_pointer)
  {
    return false;
  }
  return true;
}

// TODO: doxygen?
/// We simplify &string_constant[0] to &string_constant to facilitate expression
/// equality for exact matching.
static void clean_string_constant(exprt &expr)
{
  if(
    expr.id() == ID_index && to_index_expr(expr).index().is_zero() &&
    to_index_expr(expr).array().id() == ID_string_constant)
  {
    expr = to_index_expr(expr).array();
  }
}

// TODO: doxygen?
static void adjust_array_types(typet &type)
{
  if(type.id() != ID_pointer)
  {
    return;
  }
  const typet &subtype = to_pointer_type(type).base_type();
  if(subtype.id() == ID_array)
  {
    to_pointer_type(type).base_type() = to_array_type(subtype).element_type();
  }
  if(subtype.id() == ID_string_constant)
  {
    to_pointer_type(type).base_type() = char_type();
  }
}

// TODO: doxygen?
static exprt get_matched_base_cond(
  const exprt &shadowed_address,
  const exprt &matched_base_address,
  const namespacet &ns,
  const messaget &log)
{
  typet shadowed_address_type = shadowed_address.type();
  adjust_array_types(shadowed_address_type);
  exprt lhs =
    typecast_exprt::conditional_cast(shadowed_address, shadowed_address_type);
  exprt rhs = typecast_exprt::conditional_cast(
    matched_base_address, shadowed_address_type);
  exprt base_cond = simplify_expr(equal_exprt(lhs, rhs), ns);
  if(
    base_cond.id() == ID_equal &&
    to_equal_expr(base_cond).lhs() == to_equal_expr(base_cond).rhs())
  {
    return true_exprt();
  }
  if(base_cond.id() == ID_equal)
  {
    const equal_exprt &equal_expr = to_equal_expr(base_cond);
    const bool equality_types_match =
      equal_expr.lhs().type() == equal_expr.rhs().type();
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      equality_types_match,
      "types of expressions on each side of equality should match",
      irep_pretty_diagnosticst{equal_expr.lhs()},
      irep_pretty_diagnosticst{equal_expr.rhs()});
  }

  return base_cond;
}

// TODO: doxygen?
static exprt get_matched_expr_cond(
  const exprt &dereference_pointer,
  const exprt &expr,
  const namespacet &ns,
  const messaget &log)
{
  typet expr_type = expr.type();
  adjust_array_types(expr_type);
  exprt expr_cond = simplify_expr(
    equal_exprt(
      typecast_exprt::conditional_cast(expr, expr_type),
      typecast_exprt::conditional_cast(dereference_pointer, expr_type)),
    ns);
  if(
    expr_cond.id() == ID_equal &&
    to_equal_expr(expr_cond).lhs() == to_equal_expr(expr_cond).rhs())
  {
    return true_exprt();
  }
  if(expr_cond.id() == ID_equal)
  {
    const equal_exprt &equal_expr = to_equal_expr(expr_cond);
    const bool equality_types_match =
      equal_expr.lhs().type() == equal_expr.rhs().type();
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      equality_types_match,
      "types of expressions on each side of equality should match",
      irep_pretty_diagnosticst{equal_expr.lhs()},
      irep_pretty_diagnosticst{equal_expr.rhs()});
  }
  return expr_cond;
}

/// Retrieve the shadow value a pointer expression may point to.
/// \param shadow The shadow expression.
/// \param matched_base_descriptor The base descriptor for the shadow object.
/// \param expr The pointer expression.
/// \param ns The namespace within which we're going to perform symbol lookups.
/// \param log The message log to which we're going to print debugging messages,
///   if debugging is set.
/// \returns A `valuet` object denoting the dereferenced object within shadow
///   memory, guarded by a appropriate condition (of the form
///   pointer == &shadow_object).
static value_set_dereferencet::valuet get_shadow_dereference(
  const exprt &shadow,
  const object_descriptor_exprt &matched_base_descriptor,
  const exprt &expr,
  const namespacet &ns,
  const messaget &log)
{
  object_descriptor_exprt shadowed_object = matched_base_descriptor;
  shadowed_object.object() = shadow;
  value_set_dereferencet::valuet shadow_dereference =
    value_set_dereferencet::build_reference_to(shadowed_object, expr, ns);
#ifdef DEBUG_SM
  log.debug() << "Shadow memory: shadow-deref: "
              << format(shadow_dereference.value) << messaget::eom;
#endif
  return shadow_dereference;
}

// TODO: doxygen?
/* foreach shadowed_address in SM:
 *   if(incompatible(shadow.object, object)) continue; // Type incompatibility
 *   base_match = object == shadow_object; // Do the base obj match the SM obj
 *   if(!base_match) continue;
 *   if(object is null) continue; // Done in the caller
 *   if(type_of(dereference object is void)
 *     // we terminate as we don't know how big is the memory at that location
 *   shadowed_dereference.pointer = deref(shadow.shadowed_object, expr);
 *   aggregate the object depending on the type
 *   expr_match = shadowed_dereference == expr
 *   if(!expr_match)
 *     continue;
 *   shadow_dereference = deref(shadow.object, expr);
 *   if(expr_match)
 *     result = shadow_dereference.value [exact match]
 *     break;
 *   if(base_match) [shadow memory matches]
 *     result += (expr_match,  shadow_dereference.value)
 *     break;
 *   result += (base_match & expr_match,  shadow_dereference.value)
*/
std::vector<std::pair<exprt, exprt>> get_shadow_dereference_candidates(
  const namespacet &ns,
  const messaget &log,
  const exprt &matched_object,
  const std::vector<shadow_memory_statet::shadowed_addresst> &addresses,
  const typet &field_type,
  const exprt &expr,
  const typet &lhs_type,
  bool &exact_match)
{
  std::vector<std::pair<exprt, exprt>> result;

  for(const auto &shadowed_address : addresses)
  {
    log_try_shadow_address(ns, log, shadowed_address);
    if(!are_types_compatible(expr.type(), shadowed_address.address.type()))
    {
      log_are_types_incompatible(ns, expr, shadowed_address, log);
      continue;
    }
    const object_descriptor_exprt &matched_base_descriptor =
      to_object_descriptor_expr(matched_object);
    exprt matched_base_address =
      address_of_exprt(matched_base_descriptor.object());
    clean_string_constant(to_address_of_expr(matched_base_address).op());

    // NULL has already been handled in the caller; skip.
    if(matched_base_descriptor.object().id() == ID_null_object)
    {
      continue;
    }

    // Used only to check if the pointer is `void`
    value_set_dereferencet::valuet dereference =
      value_set_dereferencet::build_reference_to(matched_object, expr, ns);

    if(is_void_pointer(dereference.pointer.type()))
    {
      std::stringstream s;
      s << "Shadow memory: cannot get shadow memory via type void* for "
        << format(expr)
        << ". Insert a cast to the type that you want to access.";
      throw invalid_input_exceptiont(s.str());
    }

    // Replace original memory with the shadow object (symbolic dereferencing is
    // performed during symex later on).
    const value_set_dereferencet::valuet shadow_dereference =
      get_shadow_dereference(
        shadowed_address.shadow, matched_base_descriptor, expr, ns, log);
    log_value_set_match(
      ns,
      log,
      shadowed_address,
      matched_base_address,
      dereference,
      expr,
      shadow_dereference);

    const bool is_union = matched_base_descriptor.type().id() == ID_union ||
                          matched_base_descriptor.type().id() == ID_union_tag;

    exprt value;
    // Aggregate the value depending on the type
    if(field_type.id() == ID_c_bool || field_type.id() == ID_bool)
    {
      // Value is of bool type, so aggregate with or.
      value = typecast_exprt::conditional_cast(
        compute_or_over_cells(
          shadow_dereference.value, field_type, ns, log, is_union),
        lhs_type);
    }
    else
    {
      // Value is of other (bitvector) type, so aggregate with max
      value = typecast_exprt::conditional_cast(
        compute_max_over_cells(
          shadow_dereference.value, field_type, ns, log, is_union),
        lhs_type);
    }

    const exprt base_cond = get_matched_base_cond(
      shadowed_address.address, matched_base_address, ns, log);
    log_cond(ns, log, "base_cond", base_cond);
    if(base_cond.is_false())
    {
      continue;
    }

    const exprt expr_cond =
      get_matched_expr_cond(dereference.pointer, expr, ns, log);
    if(expr_cond.is_false())
    {
      continue;
    }

    if(base_cond.is_true() && expr_cond.is_true())
    {
#ifdef DEBUG_SM
      log.debug() << "exact match" << messaget::eom;
#endif
      exact_match = true;
      result.clear();
      result.emplace_back(base_cond, value);
      break;
    }

    if(base_cond.is_true())
    {
      // No point looking at further shadow addresses
      // as only one of them can match.
#ifdef DEBUG_SM
      log.debug() << "base match" << messaget::eom;
#endif
      result.clear();
      result.emplace_back(expr_cond, value);
      break;
    }
    else
    {
#ifdef DEBUG_SM
      log.debug() << "conditional match" << messaget::eom;
#endif
      result.emplace_back(and_exprt(base_cond, expr_cond), value);
    }
  }
  return result;
}

// TODO: doxygen?
// Unfortunately.
static object_descriptor_exprt
normalize(const object_descriptor_exprt &expr, const namespacet &ns)
{
  if(expr.object().id() == ID_symbol)
  {
    return expr;
  }
  if(expr.offset().id() == ID_unknown)
  {
    return expr;
  }

  object_descriptor_exprt result = expr;
  mp_integer offset =
    numeric_cast_v<mp_integer>(to_constant_expr(expr.offset()));
  exprt object = expr.object();

  while(true)
  {
    if(object.id() == ID_index)
    {
      const index_exprt &index_expr = to_index_expr(object);
      mp_integer index =
        numeric_cast_v<mp_integer>(to_constant_expr(index_expr.index()));

      offset += *pointer_offset_size(index_expr.type(), ns) * index;
      object = index_expr.array();
    }
    else if(object.id() == ID_member)
    {
      const member_exprt &member_expr = to_member_expr(object);
      const struct_typet &struct_type =
        to_struct_type(ns.follow(member_expr.struct_op().type()));
      offset +=
        *member_offset(struct_type, member_expr.get_component_name(), ns);
      object = member_expr.struct_op();
    }
    else
    {
      break;
    }
  }
  result.object() = object;
  result.offset() = from_integer(offset, expr.offset().type());
  return result;
}

bool set_field_check_null(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set,
  const exprt &expr)
{
  const null_pointer_exprt null_pointer(to_pointer_type(expr.type()));
  if(value_set.size() == 1 && contains_null_or_invalid(value_set, null_pointer))
  {
    // TODO: duplicated in log_value_set_match
#ifdef DEBUG_SM
    log.conditional_output(
      log.debug(), [ns, null_pointer, expr](messaget::mstreamt &mstream) {
        mstream << "Shadow memory: value set match: " << format(null_pointer)
                << " <-- " << format(expr) << messaget::eom;
        mstream << "Shadow memory: ignoring set field on NULL object"
                << messaget::eom;
      });
#endif
    return true;
  }
  return false;
}

/// Used for set_field and shadow memory copy
static std::vector<std::pair<exprt, exprt>>
get_shadow_memory_for_matched_object(
  const exprt &expr,
  const exprt &matched_object,
  const std::vector<shadow_memory_statet::shadowed_addresst> &addresses,
  const namespacet &ns,
  const messaget &log,
  bool &exact_match)
{
  std::vector<std::pair<exprt, exprt>> result;
  for(const auto &shadowed_address : addresses)
  {
    log_try_shadow_address(ns, log, shadowed_address);

    if(!are_types_compatible(expr.type(), shadowed_address.address.type()))
    {
#ifdef DEBUG_SM
      log.debug() << "Shadow memory: incompatible types "
                  << from_type(ns, "", expr.type()) << ", "
                  << from_type(ns, "", shadowed_address.address.type())
                  << messaget::eom;
#endif
      continue;
    }

    object_descriptor_exprt matched_base_descriptor =
      normalize(to_object_descriptor_expr(matched_object), ns);

    value_set_dereferencet::valuet dereference =
      value_set_dereferencet::build_reference_to(
        matched_base_descriptor, expr, ns);

    exprt matched_base_address =
      address_of_exprt(matched_base_descriptor.object());
    clean_string_constant(to_address_of_expr(matched_base_address).op());

    // NULL has already been handled in the caller; skip.
    if(matched_base_descriptor.object().id() == ID_null_object)
    {
      continue;
    }
    const value_set_dereferencet::valuet shadow_dereference =
      get_shadow_dereference(
        shadowed_address.shadow, matched_base_descriptor, expr, ns, log);
    log_value_set_match(
      ns,
      log,
      shadowed_address,
      matched_base_address,
      dereference,
      expr,
      shadow_dereference);

    const exprt base_cond = get_matched_base_cond(
      shadowed_address.address, matched_base_address, ns, log);
    log_cond(ns, log, "base_cond", base_cond);
    if(base_cond.is_false())
    {
      continue;
    }

    const exprt expr_cond =
      get_matched_expr_cond(dereference.pointer, expr, ns, log);
    if(expr_cond.is_false())
    {
      continue;
    }

    if(base_cond.is_true() && expr_cond.is_true())
    {
#ifdef DEBUG_SM
      log.debug() << "exact match" << messaget::eom;
#endif
      exact_match = true;
      result.clear();
      result.push_back({base_cond, shadow_dereference.pointer});
      break;
    }

    if(base_cond.is_true())
    {
      // No point looking at further shadow addresses
      // as only one of them can match.
#ifdef DEBUG_SM
      log.debug() << "base match" << messaget::eom;
#endif
      result.clear();
      result.emplace_back(expr_cond, shadow_dereference.pointer);
      break;
    }
    else
    {
#ifdef DEBUG_SM
      log.debug() << "conditional match" << messaget::eom;
#endif
      result.emplace_back(
        and_exprt(base_cond, expr_cond), shadow_dereference.pointer);
    }
  }
  return result;
}

optionalt<exprt> get_shadow_memory(
  const exprt &expr,
  const std::vector<exprt> &value_set,
  const std::vector<shadow_memory_statet::shadowed_addresst> &addresses,
  const namespacet &ns,
  const messaget &log,
  size_t &mux_size)
{
  std::vector<std::pair<exprt, exprt>> conds_values;
  for(const auto &matched_object : value_set)
  {
    if(matched_object.id() != ID_object_descriptor)
    {
      log.warning() << "Shadow memory: value set contains unknown for "
                    << format(expr) << messaget::eom;
      continue;
    }
    if(
      to_object_descriptor_expr(matched_object).root_object().id() ==
      ID_integer_address)
    {
      log.warning() << "Shadow memory: value set contains integer_address for "
                    << format(expr) << messaget::eom;
      continue;
    }
    if(matched_object.type().get_bool(ID_C_is_failed_symbol))
    {
      log.warning() << "Shadow memory: value set contains failed symbol for "
                    << format(expr) << messaget::eom;
      continue;
    }

    bool exact_match = false;
    auto per_value_set_conds_values = get_shadow_memory_for_matched_object(
      expr, matched_object, addresses, ns, log, exact_match);

    if(!per_value_set_conds_values.empty())
    {
      if(exact_match)
      {
        conds_values.clear();
      }
      conds_values.insert(
        conds_values.begin(),
        per_value_set_conds_values.begin(),
        per_value_set_conds_values.end());
      mux_size += conds_values.size() - 1;
      if(exact_match)
      {
        break;
      }
    }
  }
  if(!conds_values.empty())
  {
    return build_if_else_expr(conds_values);
  }
  return {};
}
