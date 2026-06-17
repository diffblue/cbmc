/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck_fargs.h"

#include <util/pointer_expr.h>
#include <util/std_types.h>

#include "cpp_typecheck.h"

bool cpp_typecheck_fargst::has_class_type() const
{
  for(const auto &op : operands)
  {
    if(op.type().id() == ID_struct)
      return true;
  }

  return false;
}

void cpp_typecheck_fargst::build(
  const side_effect_expr_function_callt &function_call)
{
  in_use = true;
  operands = function_call.arguments();
}

/// Structural viability check per [over.match.list] for binding a
/// brace-init-list operand to a class-typed parameter.
///
/// The viability rules implemented here:
///
///   * For empty `{}`: viable iff the destination class type has an
///     accessible default constructor (i.e., a constructor whose
///     non-`this` parameters all have default values), OR the type
///     is an aggregate with no user-declared constructors.
///
///   * For non-empty `{x_1, ..., x_n}`: viable iff
///       (a) the class has an accessible (non-explicit) constructor
///           taking `std::initializer_list<U>` (with any extra
///           parameters defaulted), in which case we trust the
///           downstream conversion in
///           `cpp_typecheckt::implicit_typecast` to typecheck each
///           operand against `U` and surface failures there; or
///       (b) the class is an aggregate (no user-declared ctors) with
///           the same number of non-static data members as operands.
///
/// We intentionally skip recursive `implicit_conversion_sequence`
/// calls during viability — that pathway both blew up the stack on
/// `<chrono>`/`<future>` template machinery and isn't necessary for
/// viability per [over.match.list]: viability is about the *kind*
/// of conversion (default-init / init_list-ctor / aggregate-init),
/// the actual conversion is the typecheck step's job.
///
/// To prevent the empty-`{}` case from selecting candidates whose
/// elaboration triggers pathological depth in standard-library
/// constexpr machinery, the empty path is restricted to class
/// types whose tag identifier does not lie under `std::chrono::`,
/// `std::tag-ratio<`, or `std::__detail::`.  This is not a
/// principled name-based filter on overload resolution per se but
/// a defensive narrowing to keep `<future>` etc. compiling while
/// the underlying recursive-elaboration depth bug is tracked
/// separately.
static bool brace_init_is_viable(
  const exprt &operand,
  const typet &target_type,
  cpp_typecheckt &cpp_typecheck)
{
  // Only brace-init operands.
  if(operand.id() != ID_initializer_list)
    return false;

  // Strip reference qualifier from target.
  typet base = target_type;
  if(is_reference(base))
    base = to_reference_type(base).base_type();

  if(base.id() != ID_struct_tag && base.id() != ID_struct)
    return false;

  // Defer std::initializer_list<T> targets to the existing
  // dedicated handler in match() and implicit_typecast.
  if(base.id() == ID_struct_tag)
  {
    const std::string id_str =
      id2string(to_struct_tag_type(base).get_identifier());
    if(id_str.find("tag-initializer_list<") != std::string::npos)
      return false;

    // Defensive narrowing for the empty-`{}` case (see helper
    // doc comment): if the destination is a chrono/ratio/__detail
    // type, do not declare empty-`{}` viable here.  Non-empty
    // brace-init is unaffected because it would not reach this
    // path (no `initializer_list<U>` ctor on those types).
    //
    // CBMC's stored struct-tag identifiers have the format
    // `<namespace-qualified-name>::tag-<class-name><...args>`;
    // the `tag-` prefix is on the unqualified class name, not on
    // the namespace.  So we look for the substring rather than
    // anchoring at position 0.
    if(operand.operands().empty())
    {
      if(
        id_str.find("std::chrono::tag-") != std::string::npos ||
        id_str.find("std::tag-ratio<") != std::string::npos ||
        id_str.find("std::__detail::tag-") != std::string::npos)
        return false;
    }
  }

  const struct_typet &class_type =
    base.id() == ID_struct_tag
      ? cpp_typecheck.follow_tag(to_struct_tag_type(base))
      : to_struct_type(base);

  // Locate components.
  bool has_user_ctor = false;
  std::size_t data_field_count = 0;
  bool has_default_ctor = false;
  bool has_init_list_ctor = false;
  for(const auto &c : class_type.components())
  {
    if(c.get_bool(ID_is_type) || c.get_bool(ID_is_static))
      continue;
    if(c.type().id() == ID_code)
    {
      if(to_code_type(c.type()).return_type().id() != ID_constructor)
        continue;
      has_user_ctor = true;
      const auto &params = to_code_type(c.type()).parameters();
      // Default ctor: only `this` parameter, or all extras
      // defaulted.
      bool all_extras_default = true;
      for(std::size_t i = 1; i < params.size(); ++i)
      {
        if(!params[i].has_default_value())
        {
          all_extras_default = false;
          break;
        }
      }
      if(all_extras_default)
        has_default_ctor = true;
      // initializer_list<U> ctor (non-explicit, params[1] is
      // tag-initializer_list<...>, optionally by reference).
      if(!c.get_bool(ID_is_explicit) && params.size() >= 2)
      {
        typet p1 = params[1].type();
        if(is_reference(p1))
          p1 = to_reference_type(p1).base_type();
        if(p1.id() == ID_struct_tag)
        {
          const std::string p1_id =
            id2string(to_struct_tag_type(p1).get_identifier());
          if(p1_id.find("tag-initializer_list<") != std::string::npos)
          {
            bool extras_default = true;
            for(std::size_t i = 2; i < params.size(); ++i)
            {
              if(!params[i].has_default_value())
              {
                extras_default = false;
                break;
              }
            }
            if(extras_default)
              has_init_list_ctor = true;
          }
        }
      }
      continue;
    }
    ++data_field_count;
  }

  if(operand.operands().empty())
  {
    // Empty `{}`: default-init or aggregate-with-no-fields.
    return has_default_ctor || (!has_user_ctor);
  }
  // Non-empty: accept if there's an init_list ctor, or aggregate
  // with matching field count.
  if(has_init_list_ctor)
    return true;
  if(!has_user_ctor && data_field_count == operand.operands().size())
    return true;
  // [over.match.list]/2.2 fallback: when no initializer-list ctor
  // is viable, the brace-init-list is treated as the argument list
  // for a regular constructor of T.  Declare the candidate viable
  // if T has a non-explicit constructor whose required-argument
  // count matches the size of the brace-init-list (extras may have
  // defaults) AND each brace-init-list element has an
  // implicit-conversion sequence to the corresponding parameter
  // type.  The actual element-by-element conversion is performed
  // in `cpp_typecheck_conversionst::implicit_typecast`'s
  // brace-init-to-class branch, which materialises the result as
  // a member-wise struct expression.
  //
  // [over.match.list]/3: in copy-list-initialization, if an
  // explicit constructor is chosen, the program is ill-formed.
  // `cpp_typecheck_fargst::match` is invoked when matching arguments
  // to function parameters, which is copy-list-initialization;
  // accordingly, explicit ctors are excluded here.  The standard
  // technically requires explicit ctors to be in the candidate set
  // (and the ill-formedness emerges only when one is selected), but
  // CBMC's overload-resolution machinery does not distinguish
  // "selected but ill-formed" from "selected".  Excluding explicit
  // ctors here matches the practical outcome of the standard rule.
  {
    const std::size_t n_args = operand.operands().size();
    for(const auto &c : class_type.components())
    {
      if(c.type().id() != ID_code)
        continue;
      if(to_code_type(c.type()).return_type().id() != ID_constructor)
        continue;
      if(c.get_bool(ID_is_explicit))
        continue;
      const auto &params = to_code_type(c.type()).parameters();
      if(params.size() < 2)
        continue; // only `this`, would be the default ctor
      const std::size_t formal_count = params.size() - 1;
      if(n_args > formal_count)
        continue;
      // count required (non-defaulted) parameters from the front
      std::size_t required = formal_count;
      for(std::size_t i = params.size() - 1; i >= 1 && required > 0; --i)
      {
        if(params[i].has_default_value())
          --required;
        else
          break;
      }
      if(n_args < required || n_args > formal_count)
        continue;
      // Check element-by-element ICS to parameter types.
      bool args_compatible = true;
      for(std::size_t i = 0; i < n_args; ++i)
      {
        exprt new_expr;
        unsigned rank = 0;
        exprt op_copy = operand.operands()[i];
        if(!cpp_typecheck.implicit_conversion_sequence(
             op_copy, params[i + 1].type(), new_expr, rank))
        {
          args_compatible = false;
          break;
        }
      }
      if(args_compatible)
        return true;
    }
  }
  return false;
}

/// [over.ics.list]/4: a brace-init-list `{e1, ..., en}` has a viable
/// implicit conversion sequence to `std::initializer_list<X>` iff
/// every element `ei` has an implicit conversion sequence to `X`.
/// The empty brace `{}` is always viable (yields an empty
/// initializer-list).
///
/// This check is intentionally limited to standard ICS via
/// `implicit_conversion_sequence`; it does not recurse into nested
/// list-initializations of `X`.  That mirrors the conversion
/// performed at the call site
/// (`cpp_typecheck_conversionst::implicit_typecast`'s
/// brace-to-initializer_list branch), which calls
/// `implicit_typecast(val, elem_type)` per element.
static bool brace_init_to_init_list_is_viable(
  const exprt &operand,
  const typet &target_type,
  cpp_typecheckt &cpp_typecheck)
{
  if(operand.id() != ID_initializer_list)
    return false;
  if(target_type.id() != ID_struct_tag)
    return false;
  const std::string id_str =
    id2string(to_struct_tag_type(target_type).get_identifier());
  if(id_str.find("tag-initializer_list<") == std::string::npos)
    return false;

  // Empty brace is always viable.
  if(operand.operands().empty())
    return true;

  // Locate the element type from the `_begin` / `_M_array` member.
  const struct_typet &struct_type =
    cpp_typecheck.follow_tag(to_struct_tag_type(target_type));
  typet elem_type;
  bool found = false;
  for(const auto &c : struct_type.components())
  {
    if(
      (c.get_base_name() == "_begin" || c.get_base_name() == "_M_array") &&
      c.type().id() == ID_pointer)
    {
      elem_type = to_pointer_type(c.type()).base_type();
      elem_type.remove(ID_C_constant);
      found = true;
      break;
    }
  }
  if(!found)
    return false;

  // Each element must have an ICS to `elem_type`.
  for(const auto &op : operand.operands())
  {
    exprt new_expr;
    unsigned rank = 0;
    exprt op_copy = op;
    if(!cpp_typecheck.implicit_conversion_sequence(
         op_copy, elem_type, new_expr, rank))
      return false;
  }
  return true;
}

bool cpp_typecheck_fargst::match(
  const code_typet &code_type,
  unsigned &distance,
  cpp_typecheckt &cpp_typecheck) const
{
  distance = 0;

  exprt::operandst ops = operands;
  const code_typet::parameterst &parameters = code_type.parameters();

  if(parameters.size() > ops.size())
  {
    // Check for default values.
    // Don't push the actual default value expressions into ops —
    // they may contain unresolved template parameters. Just verify
    // that default values exist for the extra parameters.
    for(std::size_t i = ops.size(); i < parameters.size(); i++)
    {
      const exprt &default_value = parameters[i].default_value();

      // [over.match.viable]/2.2: a candidate function with more
      // parameters than there are arguments is viable only if each
      // parameter without a corresponding argument has a default
      // argument.  A genuine default argument is a proper expression;
      // a nil or empty-id expression is not a default argument.  The
      // latter can appear on the parameters of a function type that is
      // synthesised during template argument deduction
      // (`guess_function_template_args`), where a parameter with no
      // default ends up carrying an empty `exprt` rather than a
      // `nil_exprt`.  Treating that as a default argument would make,
      // e.g., the four-parameter tag-dispatch overload
      // `__find_if(_It, _It, _Pred, random_access_iterator_tag)`
      // wrongly viable for the three-argument call
      // `__find_if(first, last, pred)`, leaving the call ambiguous with
      // the genuine three-parameter overload.
      if(default_value.is_nil() || default_value.id().empty())
        return false;
    }
  }
  else if(parameters.size() < ops.size())
  {
    // check for ellipsis
    if(!code_type.has_ellipsis())
      return false;
  }

  exprt::operandst::iterator it = ops.begin();
  for(const auto &parameter : parameters)
  {
    if(it == ops.end())
      break; // remaining parameters have default values
    // read
    // http://publib.boulder.ibm.com/infocenter/comphelp/v8v101/topic/
    //   com.ibm.xlcpp8a.doc/language/ref/implicit_conversion_sequences.htm
    //
    // The following are the three categories of conversion sequences
    // in order from best to worst:
    // * Standard conversion sequences
    // * User-defined conversion sequences
    // * Ellipsis conversion sequences

    const exprt &operand = *it;
    typet type = parameter.type();

#if 0
    // unclear, todo
    if(is_reference(operand.type()))
      std::cout << "O: " << operand.pretty() << '\n';

    assert(!is_reference(operand.type()));
#endif

    // "this" is a special case -- we turn the pointer type
    // into a reference type to do the type matching
    if(it == ops.begin() && parameter.get_this())
    {
      type.set(ID_C_reference, true);
      type.set(ID_C_this, true);
    }

    unsigned rank = 0;
    exprt new_expr;

#if 0
    std::cout << "C: " << cpp_typecheck.to_string(operand.type())
              << " -> " << cpp_typecheck.to_string(parameter.type())
              << '\n';
#endif

    // can we do the standard conversion sequence?
    if(cpp_typecheck.implicit_conversion_sequence(
         operand, type, new_expr, rank))
    {
      // ok
      distance += rank;
#if 0
      std::cout << "OK " << rank << '\n';
#endif
    }
    else if(
      operand.id() == ID_initializer_list && cpp_typecheck.cpp_is_pod(type) &&
      operand.operands().size() == 1 &&
      cpp_typecheck.implicit_conversion_sequence(
        to_unary_expr(operand).op(), type, new_expr, rank))
    {
      distance += rank;
    }
    else if(
      operand.id() == ID_initializer_list && type.id() == ID_struct_tag &&
      id2string(to_struct_tag_type(type).get_identifier())
          .find("tag-initializer_list<") != std::string::npos &&
      brace_init_to_init_list_is_viable(operand, type, cpp_typecheck))
    {
      // [over.ics.list]/4: brace-init-list to `std::initializer_list<X>`
      // is a viable conversion only if every element of the list has
      // an implicit-conversion sequence to `X`.  Without that
      // element-by-element check, the overload appears viable for
      // any 2+ -element list and beats more specific overloads
      // such as `insert(const value_type&)` on a class type:
      // for example `unordered_map<K,V>::insert({k, idx})` would
      // pick `insert(initializer_list<pair<const K,V>>)` and fail
      // because `k` is a `K`, not a `pair<const K, V>`.
      distance += 1;
    }
    else if(
      operand.id() == ID_initializer_list &&
      brace_init_is_viable(operand, type, cpp_typecheck))
    {
      // C++11 [over.match.list] list-initialization: brace-init
      // initialising a class-typed parameter (or reference to one)
      // via either a default constructor (empty `{}`), an
      // accessible `initializer_list<U>` constructor (non-empty
      // brace), or aggregate initialisation.  See
      // `brace_init_is_viable` for the full set of conditions and
      // the design notes on chrono/ratio/__detail narrowing.
      //
      // Use distance 4 (worse than a standard conversion but
      // better than ellipsis).  For prvalue source (a temporary
      // materialised from the brace-init-list), [over.ics.rank]/
      // 3.3.4 prefers an rvalue-reference target over a (const)
      // lvalue-reference target.  Bias the rank by -1 for an
      // rvalue-ref target so that, when the same `brace_init_is_viable`
      // candidate is otherwise equally viable, the rvalue-ref
      // overload wins (otherwise CBMC reports
      // `symbol 'X' does not uniquely resolve` between
      // `f(const T&)` and `f(T&&)`).
      distance += 4;
      if(is_rvalue_reference(type))
        distance -= 1;
    }
    else
    {
      return false; // no conversion possible
    }

    ++it;
  }

  // we may not have used all operands
  for(; it != ops.end(); ++it)
    // Ellipsis is the 'worst' of the conversion sequences
    distance += 1000;

  return true;
}
