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
  in_use=true;
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
  return false;
}

bool cpp_typecheck_fargst::match(
  const code_typet &code_type,
  unsigned &distance,
  cpp_typecheckt &cpp_typecheck) const
{
  distance=0;

  exprt::operandst ops=operands;
  const code_typet::parameterst &parameters=code_type.parameters();

  if(parameters.size()>ops.size())
  {
    // Check for default values.
    // Don't push the actual default value expressions into ops —
    // they may contain unresolved template parameters. Just verify
    // that default values exist for the extra parameters.
    for(std::size_t i=ops.size(); i<parameters.size(); i++)
    {
      const exprt &default_value=
        parameters[i].default_value();

      if(default_value.is_nil())
        return false;
    }
  }
  else if(parameters.size()<ops.size())
  {
    // check for ellipsis
    if(!code_type.has_ellipsis())
      return false;
  }

  exprt::operandst::iterator it=ops.begin();
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

    const exprt &operand=*it;
    typet type=parameter.type();

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

    unsigned rank=0;
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
      distance+=rank;
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
          .find("tag-initializer_list<") != std::string::npos)
    {
      // Brace-init-list to std::initializer_list<T> conversion
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
      // better than ellipsis).
      distance += 4;
    }
    else
    {
      return false; // no conversion possible
    }

    ++it;
  }

  // we may not have used all operands
  for( ; it!=ops.end(); ++it)
    // Ellipsis is the 'worst' of the conversion sequences
    distance+=1000;

  return true;
}
