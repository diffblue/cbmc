/*******************************************************************\

Module: C++ Language Type Checking

Author: Kiro

\*******************************************************************/

/// \file
/// C++ Language Type Checking: the allocation function of a new-expression
/// and the deallocation function of a delete-expression

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/symbol_table_base.h>

#include <ansi-c/padding.h>

#include "cpp_sfinae_context.h"
#include "cpp_typecheck.h"

#include <algorithm>

/// \return whether \p type is std::size_t, the type of the first parameter
///   of an allocation function ([basic.stc.dynamic.allocation]/1)
static bool is_size_parameter(const typet &type)
{
  return type.id() == ID_unsignedbv &&
         to_unsignedbv_type(type).get_width() == size_type().get_width();
}

/// \return whether \p type is std::align_val_t ([new.syn])
static bool is_align_val_parameter(const typet &type)
{
  return type.id() == ID_c_enum_tag &&
         to_c_enum_tag_type(type).get_identifier() == "std::tag-align_val_t";
}

/// \return whether \p type is `const std::nothrow_t &` ([new.syn])
static bool is_nothrow_parameter(const typet &type)
{
  if(!is_reference(type))
    return false;
  const typet &base = to_reference_type(type).base_type();
  return base.id() == ID_struct_tag &&
         to_struct_tag_type(base).get_identifier() == "std::tag-nothrow_t";
}

/// \return whether \p type is std::destroying_delete_t ([new.syn])
static bool is_destroying_delete_parameter(const typet &type)
{
  return type.id() == ID_struct_tag &&
         to_struct_tag_type(type).get_identifier() ==
           "std::tag-destroying_delete_t";
}

/// \return whether \p type is `void *` (not a reference)
static bool is_pointer_to_void(const typet &type)
{
  return type.id() == ID_pointer && !is_reference(type) &&
         to_pointer_type(type).base_type().id() == ID_empty;
}

/// \return whether \p symbol declares a function of the global scope (not a
///   class member, not in a namespace) named \p operator_name
static bool
is_global_function(const symbolt &symbol, const std::string &operator_name)
{
  if(symbol.type.id() != ID_code)
    return false;
  if(!symbol.type.get(ID_C_member_name).empty())
    return false;
  // the identifier of a global function is its name followed by its
  // signature; one declared in a namespace has the namespace prefix
  const std::string &name = id2string(symbol.name);
  return name.compare(0, operator_name.size() + 1, operator_name + "(") == 0;
}

/// N5008 [new.delete.single]/1-12, [new.delete.array]/1-11: the replaceable
/// global allocation functions take the size, optionally the alignment,
/// optionally a `const std::nothrow_t &`.
static bool is_replaceable_allocation_function(const symbolt &symbol)
{
  if(
    !is_global_function(symbol, "operatorcpp_new") &&
    !is_global_function(symbol, "operatorcpp_new[]"))
  {
    return false;
  }
  const auto &parameters = to_code_type(symbol.type).parameters();
  std::size_t i = 0;
  if(i == parameters.size() || !is_size_parameter(parameters[i].type()))
    return false;
  ++i;
  if(i < parameters.size() && is_align_val_parameter(parameters[i].type()))
    ++i;
  if(i < parameters.size() && is_nothrow_parameter(parameters[i].type()))
    ++i;
  return i == parameters.size();
}

/// N5008 [new.delete.placement]/2, /5: the reserved placement allocation
/// functions `operator new(std::size_t, void *)` and its array form, which
/// return their pointer argument and may not be displaced ([new.delete.
/// placement]/1)
static bool is_reserved_placement_allocation_function(const symbolt &symbol)
{
  if(
    !is_global_function(symbol, "operatorcpp_new") &&
    !is_global_function(symbol, "operatorcpp_new[]"))
  {
    return false;
  }
  const auto &parameters = to_code_type(symbol.type).parameters();
  return parameters.size() == 2 && is_size_parameter(parameters[0].type()) &&
         is_pointer_to_void(parameters[1].type());
}

/// N5008 [basic.align]/3: the alignment that the implementation guarantees
/// without an alignment argument, __STDCPP_DEFAULT_NEW_ALIGNMENT__
/// ([cpp.predefined]/1); a type with a stricter alignment has new-extended
/// alignment.  The values are those the compilers predefine: 16 for GCC on
/// any target, twice the size of a pointer for Clang and Visual Studio.
static mp_integer default_new_alignment()
{
  if(config.ansi_c.mode == configt::ansi_ct::flavourt::GCC)
    return 16;
  return 2 * config.ansi_c.pointer_width / config.ansi_c.char_width;
}

/// N5008 [expr.new]/21: the array allocation overhead, the Itanium C++
/// ABI's array cookie: the size of std::size_t, or the alignment of the
/// elements if that is larger, so that they stay aligned
static mp_integer array_cookie_size(const mp_integer &element_alignment)
{
  return std::max(
    mp_integer{size_type().get_width() / config.ansi_c.char_width},
    element_alignment);
}

/// N5008 [basic.stc.dynamic.deallocation]/3: a usual deallocation function
/// takes `void *` (or, for a destroying operator delete, a pointer to its
/// class followed by std::destroying_delete_t), optionally the size,
/// optionally the alignment, and is not a template instance.
static bool is_usual_deallocation_function(
  const symbolt &symbol,
  bool &destroying,
  bool &sized,
  bool &aligned)
{
  if(symbol.type.id() != ID_code || symbol.type.get_bool(ID_C_template))
    return false;
  const auto &parameters = to_code_type(symbol.type).parameters();
  std::size_t i = 0;
  destroying = parameters.size() >= 2 &&
               parameters[0].type().id() == ID_pointer &&
               !is_reference(parameters[0].type()) &&
               is_destroying_delete_parameter(parameters[1].type());
  if(destroying)
    i = 2;
  else if(!parameters.empty() && is_pointer_to_void(parameters[0].type()))
    i = 1;
  else
    return false;
  sized = i < parameters.size() && is_size_parameter(parameters[i].type());
  if(sized)
    ++i;
  aligned =
    i < parameters.size() && is_align_val_parameter(parameters[i].type());
  if(aligned)
    ++i;
  return i == parameters.size();
}

/// \return a name that searches the operator \p operator_id in the class
///   \p class_id, or in the global scope if \p class_id is empty
static cpp_namet
qualified_operator_name(const irep_idt &class_id, const irep_idt &operator_id)
{
  cpp_namet name;
  if(class_id.empty())
    name.get_sub().push_back(irept{ID_scope_resolution});
  else
  {
    // the class's identifier: resolve_scope finds it in the id map
    cpp_namet::namet class_name{class_id};
    name.get_sub().push_back(class_name);
    name.get_sub().push_back(irept{ID_scope_resolution});
  }
  name.get_sub().push_back(irept{ID_operator});
  name.get_sub().push_back(irept{operator_id});
  return name;
}

/// \return whether a search for \p base_name in the scope of the class
///   \p class_id ([class.member.lookup]) finds a declaration
bool cpp_typecheckt::class_scope_declares(
  const irep_idt &class_id,
  const irep_idt &base_name)
{
  const auto it = cpp_scopes.id_map.find(class_id);
  if(it == cpp_scopes.id_map.end())
    return false;
  return !static_cast<cpp_scopet &>(*it->second)
            .lookup(base_name, cpp_scopet::QUALIFIED)
            .empty();
}

/// N5008 [expr.new]/12-13, /20: select the allocation function of the
/// new-expression \p expr (type-checked except for the allocation), whose
/// allocated type is \p allocated_type, by overload resolution on the call
/// `operator new(size, [alignment,] placement-args...)` (`operator new[]`
/// for an array).  The new-expression keeps the built-in lowering when the
/// selected function is a replaceable global allocation function, whose
/// call an implementation may omit ([expr.new]/14), or the reserved
/// placement form (its single operand being the converted pointer
/// argument).  Any other function -- a class-specific one ([class.free]),
/// or a global one with other parameters -- is called: the call is
/// recorded as ID_allocation_function, with a placeholder for the size,
/// which goto conversion computes.
void cpp_typecheckt::resolve_allocation_function(
  exprt &expr,
  const typet &allocated_type)
{
  const bool is_array = expr.get(ID_statement) == ID_cpp_new_array;
  const irep_idt operator_id = is_array ? ID_cpp_new_array : ID_cpp_new;
  const irep_idt base_name = is_array ? "operatorcpp_new[]" : "operatorcpp_new";
  const source_locationt &source_location = expr.source_location();

  // [expr.new]/13: the class whose scope is searched first
  typet element_type = allocated_type;
  while(element_type.id() == ID_array)
    element_type = to_array_type(element_type).element_type();
  irep_idt class_id;
  if(
    !expr.get_bool(ID_C_global_scope) && element_type.id() == ID_struct_tag &&
    class_scope_declares(
      to_struct_tag_type(element_type).get_identifier(), base_name))
  {
    class_id = to_struct_tag_type(element_type).get_identifier();
  }
  cpp_namet operator_name = qualified_operator_name(class_id, operator_id);
  operator_name.add(ID_C_source_location) = source_location;
  for(auto &component : operator_name.get_sub())
    component.add(ID_C_source_location) = source_location;
  const exprt name =
    static_cast<const exprt &>(static_cast<const irept &>(operator_name));

  // [expr.new]/20: the size, then the alignment if the type has
  // new-extended alignment, then the placement arguments; if that finds no
  // function, without (resp. with) the alignment
  const exprt size_argument =
    side_effect_expr_nondett{size_type(), source_location};
  std::optional<exprt> alignment_argument;
  bool new_extended_alignment = false;
  if(config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP17)
  {
    const mp_integer alignment_value = alignment(allocated_type, *this).get();
    new_extended_alignment = alignment_value > default_new_alignment();
    alignment_argument = typecast_exprt{
      from_integer(alignment_value, size_type()),
      c_enum_tag_typet{"std::tag-align_val_t"}};
  }
  const exprt::operandst placement_arguments = expr.operands();
  auto argument_list = [&](bool with_alignment)
  {
    exprt::operandst arguments{size_argument};
    if(with_alignment)
      arguments.push_back(*alignment_argument);
    for(const auto &argument : placement_arguments)
      arguments.push_back(already_typechecked_exprt{argument});
    return arguments;
  };
  std::vector<bool> attempts{new_extended_alignment};
  if(alignment_argument.has_value())
    attempts.push_back(!new_extended_alignment);

  std::optional<side_effect_expr_function_callt> call;
  for(const bool with_alignment : attempts)
  {
    side_effect_expr_function_callt attempt{
      name, argument_list(with_alignment), typet{}, source_location};
    try
    {
      sfinae_contextt guard{*this};
      typecheck_side_effect_function_call(attempt);
    }
    catch(...)
    {
      continue;
    }
    call = std::move(attempt);
    break;
  }
  if(!call.has_value())
  {
    // diagnose the first form ([expr.new]/20: the program is ill-formed)
    side_effect_expr_function_callt attempt{
      name, argument_list(attempts.front()), typet{}, source_location};
    typecheck_side_effect_function_call(attempt);
    error().source_location = source_location;
    error() << "no matching allocation function" << eom;
    throw 0;
  }

  const exprt &function = call->function();
  const symbolt *selected =
    function.id() == ID_symbol
      ? symbol_table.lookup(to_symbol_expr(function).get_identifier())
      : nullptr;
  if(selected == nullptr)
  {
    error().source_location = source_location;
    error() << "allocation function is not a function" << eom;
    throw 0;
  }

  if(is_replaceable_allocation_function(*selected))
  {
    // [expr.new]/14: the call is omitted, the storage provided by the
    // implementation (__new, __new_array)
    expr.operands().clear();
    return;
  }
  if(is_reserved_placement_allocation_function(*selected))
  {
    // the converted pointer argument
    expr.operands() = {call->arguments().back()};
    return;
  }

  // [expr.new]/22: a non-throwing allocation function indicates failure by
  // returning null
  needed_exception_specification(selected->name);
  const typet &selected_type = symbol_table.lookup_ref(selected->name).type;
  if(
    selected_type.get_bool("#C_noexcept") ||
    selected_type.get_bool(ID_noexcept))
  {
    expr.set("#allocation_noexcept", true);
  }
  // [expr.new]/21: an array allocation may request more than the elements
  // need; it stores the number of elements in front of them (the Itanium
  // C++ ABI's array cookie) when the class's own allocation function is
  // used and the elements have a non-trivial destructor, so that a
  // delete-expression using the class's deallocation function knows how
  // many to destroy
  if(is_array && !class_id.empty())
  {
    exprt element(ID_new_object, element_type);
    element.set(ID_C_lvalue, true);
    if(cpp_destructor(source_location, element, false).has_value())
    {
      const mp_integer cookie =
        array_cookie_size(alignment(element_type, *this).get());
      expr.add("#array_cookie") = from_integer(cookie, size_type());
    }
  }
  resolve_new_expression_deallocation(expr, *selected, element_type);
  expr.operands().clear();
  expr.add(ID_allocation_function) = std::move(*call);
}

/// N5008 [expr.new]/27-30: the deallocation function that the new-expression
/// \p expr calls if the initialization of the object terminates by throwing
/// an exception, recorded as ID_deallocation_function with the arguments
/// besides the pointer (none, but "#deallocation_placement" for a placement
/// deallocation function, which receives the placement arguments again).
/// \p allocation_function is the allocation function called, \p element_type
/// the allocated (element) type.
void cpp_typecheckt::resolve_new_expression_deallocation(
  exprt &expr,
  const symbolt &allocation_function,
  const typet &element_type)
{
  const bool is_array = expr.get(ID_statement) == ID_cpp_new_array;
  const irep_idt base_name =
    is_array ? "operatorcpp_delete[]" : "operatorcpp_delete";
  const source_locationt &source_location = expr.source_location();

  // [expr.new]/28: the class scope unless the expression begins with `::',
  // the global scope otherwise or if nothing is found
  cpp_scopet::id_sett found;
  bool class_scope = false;
  if(!expr.get_bool(ID_C_global_scope) && element_type.id() == ID_struct_tag)
  {
    const auto it =
      cpp_scopes.id_map.find(to_struct_tag_type(element_type).get_identifier());
    if(it != cpp_scopes.id_map.end())
    {
      found = static_cast<cpp_scopet &>(*it->second)
                .lookup(base_name, cpp_scopet::QUALIFIED);
      class_scope = !found.empty();
    }
  }
  if(found.empty())
    found =
      cpp_scopes.get_root_scope().lookup(base_name, cpp_scopet::QUALIFIED);

  const auto &allocation_parameters =
    to_code_type(allocation_function.type).parameters();
  if(!expr.operands().empty())
  {
    // [expr.new]/29: a placement deallocation function matches a placement
    // allocation function if it has the same number of parameters and all
    // parameter types but the first are identical; it is called only if the
    // match is unique
    const symbolt *match = nullptr;
    std::size_t matches = 0;
    for(const auto &id : found)
    {
      const symbolt *symbol = symbol_table.lookup(id->identifier);
      if(symbol == nullptr || symbol->type.id() != ID_code)
        continue;
      const auto &parameters = to_code_type(symbol->type).parameters();
      if(
        parameters.size() != allocation_parameters.size() ||
        parameters.empty() || !is_pointer_to_void(parameters[0].type()))
      {
        continue;
      }
      bool identical = true;
      for(std::size_t i = 1; i < parameters.size(); ++i)
      {
        if(parameters[i].type() != allocation_parameters[i].type())
          identical = false;
      }
      if(identical)
      {
        match = symbol;
        ++matches;
      }
    }
    if(matches != 1)
      return;
    // [expr.new]/29: ill-formed if that is a usual deallocation function
    bool destroying, sized, aligned;
    if(is_usual_deallocation_function(*match, destroying, sized, aligned))
    {
      error().source_location = source_location;
      error() << "the usual deallocation function '" << match->display_name()
              << "' matches the placement allocation function '"
              << allocation_function.display_name() << "'" << eom;
      throw 0;
    }
    expr.add(ID_deallocation_function) = match->symbol_expr();
    expr.set("#deallocation_placement", true);
    return;
  }

  // [expr.new]/29: for a non-placement allocation function the usual
  // deallocation function, as for a delete-expression ([expr.delete]/9),
  // but not a destroying operator delete: there is no object to destroy
  if(!class_scope)
  {
    // the global usual deallocation functions are the replaceable ones
    // (built in: __delete, __delete_array)
    expr.add(ID_deallocation_function) =
      lookup(is_array ? "__delete_array" : "__delete").symbol_expr();
    return;
  }
  const auto selected = select_usual_deallocation_function(
    found, element_type, false, source_location);
  if(!selected.has_value())
    return;
  expr.add(ID_deallocation_function) = selected->symbol->symbol_expr();
  if(selected->sized)
    expr.set("#deallocation_sized", true);
  irept &arguments = expr.add(ID_arguments);
  for(auto &argument :
      usual_deallocation_arguments(*selected, element_type, source_location))
  {
    arguments.get_sub().push_back(std::move(argument));
  }
}

/// N5008 [expr.delete]/8-9: select among the declarations \p found by the
/// search for a deallocation function the usual deallocation function to
/// call for an object of type \p element_type.  \p allow_destroying:
/// whether a destroying operator delete is a candidate (not for the
/// deallocation of a new-expression whose initialization throws, which has
/// no object to destroy).
/// \return the function, or nothing if \p found has no usual deallocation
///   function
std::optional<cpp_typecheckt::usual_deallocationt>
cpp_typecheckt::select_usual_deallocation_function(
  const cpp_scopet::id_sett &found,
  const typet &element_type,
  bool allow_destroying,
  const source_locationt &source_location)
{
  // [expr.delete]/8: only the usual deallocation functions are candidates
  std::vector<usual_deallocationt> candidates;
  for(const auto &id : found)
  {
    const symbolt *symbol = symbol_table.lookup(id->identifier);
    usual_deallocationt candidate{symbol, false, false, false};
    if(
      symbol != nullptr &&
      is_usual_deallocation_function(
        *symbol, candidate.destroying, candidate.sized, candidate.aligned) &&
      (allow_destroying || !candidate.destroying))
    {
      candidates.push_back(candidate);
    }
  }
  if(candidates.empty())
    return {};

  // [expr.delete]/9.1: a destroying operator delete is preferred
  if(std::any_of(
       candidates.begin(),
       candidates.end(),
       [](const usual_deallocationt &c) { return c.destroying; }))
  {
    candidates.erase(
      std::remove_if(
        candidates.begin(),
        candidates.end(),
        [](const usual_deallocationt &c) { return !c.destroying; }),
      candidates.end());
  }
  // [expr.delete]/9.2: a function with an alignment parameter if the type
  // has new-extended alignment, one without otherwise
  const bool new_extended_alignment =
    config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP17 &&
    alignment(element_type, *this).get() > default_new_alignment();
  if(std::any_of(
       candidates.begin(),
       candidates.end(),
       [&](const usual_deallocationt &c)
       { return c.aligned == new_extended_alignment; }))
  {
    candidates.erase(
      std::remove_if(
        candidates.begin(),
        candidates.end(),
        [&](const usual_deallocationt &c)
        { return c.aligned != new_extended_alignment; }),
      candidates.end());
  }
  // [expr.delete]/9.3-9.4: of the functions of a class scope, the one
  // without a size parameter
  if(candidates.size() > 1)
  {
    candidates.erase(
      std::remove_if(
        candidates.begin(),
        candidates.end(),
        [](const usual_deallocationt &c) { return c.sized; }),
      candidates.end());
  }
  if(candidates.size() != 1)
  {
    error().source_location = source_location;
    error() << "ambiguous deallocation function for '"
            << to_string(element_type) << "'" << eom;
    throw 0;
  }
  return candidates.front();
}

/// N5008 [expr.delete]/10: the arguments of a call of the usual deallocation
/// function \p selected besides the pointer: an unspecified value of type
/// std::destroying_delete_t, the size of an object of type \p element_type
/// (that of an array is computed by goto conversion), and its alignment, as
/// far as the function takes them.
exprt::operandst cpp_typecheckt::usual_deallocation_arguments(
  const usual_deallocationt &selected,
  const typet &element_type,
  const source_locationt &source_location)
{
  exprt::operandst arguments;
  const auto &parameters = to_code_type(selected.symbol->type).parameters();
  std::size_t i = 1;
  if(selected.destroying)
  {
    arguments.push_back(
      side_effect_expr_nondett{parameters[i].type(), source_location});
    ++i;
  }
  if(selected.sized)
  {
    auto size = size_of_expr(element_type, *this);
    if(!size.has_value())
    {
      error().source_location = source_location;
      error() << "size of deallocated object is not known" << eom;
      throw 0;
    }
    arguments.push_back(
      typecast_exprt::conditional_cast(*size, parameters[i].type()));
    ++i;
  }
  if(selected.aligned)
  {
    arguments.push_back(typecast_exprt{
      from_integer(alignment(element_type, *this).get(), size_type()),
      parameters[i].type()});
  }
  return arguments;
}

/// N5008 [expr.delete]/7-10: select the deallocation function of the
/// delete-expression \p expr whose operand points to \p deleted_type.  The
/// search starts in the scope of a class \p deleted_type unless the
/// expression begins with `::`; the global usual deallocation functions
/// are all replaceable, and a delete-expression using one keeps the
/// built-in lowering, which matches the omitted allocation of a
/// new-expression ([expr.delete]/6.3).  A class-specific one is recorded
/// as ID_deallocation_function, with the arguments it takes besides the
/// pointer.  The selection at the point of definition of a virtual
/// destructor ([expr.delete]/8.1) is not modelled: the search uses the
/// static type.
void cpp_typecheckt::resolve_deallocation_function(
  exprt &expr,
  const typet &deleted_type)
{
  const bool is_array = expr.get(ID_statement) == ID_cpp_delete_array;
  typet element_type = deleted_type;
  while(element_type.id() == ID_array)
    element_type = to_array_type(element_type).element_type();
  if(expr.get_bool(ID_C_global_scope) || element_type.id() != ID_struct_tag)
    return;
  const irep_idt &class_id = to_struct_tag_type(element_type).get_identifier();
  const irep_idt base_name =
    is_array ? "operatorcpp_delete[]" : "operatorcpp_delete";
  const auto scope_it = cpp_scopes.id_map.find(class_id);
  if(scope_it == cpp_scopes.id_map.end())
    return;
  const auto found = static_cast<cpp_scopet &>(*scope_it->second)
                       .lookup(base_name, cpp_scopet::QUALIFIED);
  if(found.empty())
    return;

  const source_locationt &source_location = expr.source_location();
  const auto selected_opt = select_usual_deallocation_function(
    found, element_type, true, source_location);
  if(!selected_opt.has_value())
  {
    // [expr.delete]/8 Note 5: a class with only placement deallocation
    // functions makes the lookup set empty
    error().source_location = source_location;
    error() << "no usual deallocation function '"
            << (is_array ? "operator delete[]" : "operator delete")
            << "' in class '" << to_string(element_type) << "'" << eom;
    throw 0;
  }
  const usual_deallocationt &selected = *selected_opt;

  // [expr.delete]/9: the selected function shall be accessible
  const struct_typet &class_type = follow_tag(to_struct_tag_type(element_type));
  for(const auto &component : class_type.components())
  {
    if(
      component.get_name() == selected.symbol->name &&
      check_component_access(component, class_type))
    {
      error().source_location = source_location;
      error() << "deallocation function '" << selected.symbol->display_name()
              << "' is not accessible" << eom;
      throw 0;
    }
  }

  // [expr.delete]/10: the arguments besides the pointer
  exprt::operandst arguments =
    usual_deallocation_arguments(selected, element_type, source_location);
  if(selected.sized)
    expr.set("#deallocation_sized", true);

  expr.add(ID_deallocation_function) = selected.symbol->symbol_expr();
  irept &recorded_arguments = expr.add(ID_arguments);
  for(auto &argument : arguments)
    recorded_arguments.get_sub().push_back(std::move(argument));
  if(selected.destroying)
  {
    // [expr.delete]/5: no destructor is invoked
    expr.set("#destroying_delete", true);
    expr.set(ID_destructor, nil_exprt{});
  }

  // the array cookie, if the class's allocation function stores one
  // (resolve_allocation_function)
  if(is_array && class_scope_declares(class_id, "operatorcpp_new[]"))
  {
    const irept &destructor = expr.find(ID_destructor);
    if(destructor.is_not_nil())
    {
      const mp_integer cookie =
        array_cookie_size(alignment(element_type, *this).get());
      expr.add("#array_cookie") = from_integer(cookie, size_type());
    }
  }
}
