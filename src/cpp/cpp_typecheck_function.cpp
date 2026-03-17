/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_name.h"
#include "cpp_template_type.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"

void cpp_typecheckt::convert_parameter(
  const irep_idt &current_mode,
  code_typet::parametert &parameter)
{
  irep_idt base_name=id2string(parameter.get_base_name());

  if(base_name.empty())
  {
    base_name="#anon_arg"+std::to_string(anon_counter++);
    parameter.set_base_name(base_name);
  }

  PRECONDITION(!cpp_scopes.current_scope().prefix.empty());
  irep_idt identifier=cpp_scopes.current_scope().prefix+
                      id2string(base_name);

  parameter.set_identifier(identifier);

  // the parameter may already have been set up if dealing with virtual methods
  const symbolt *check_symbol;
  if(!lookup(identifier, check_symbol))
    return;

  parameter_symbolt symbol;

  symbol.name=identifier;
  symbol.base_name=parameter.get_base_name();
  symbol.location=parameter.source_location();
  symbol.mode = current_mode;
  symbol.module=module;
  symbol.type=parameter.type();
  symbol.is_lvalue=!is_reference(symbol.type);

  INVARIANT(!symbol.base_name.empty(), "parameter has base name");

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::convert_parameter: symbol_table.move(\""
            << symbol.name << "\") failed" << eom;
    throw 0;
  }

  // put into scope
  cpp_scopes.put_into_scope(*new_symbol);
}

void cpp_typecheckt::convert_parameters(
  const irep_idt &current_mode,
  code_typet &function_type)
{
  code_typet::parameterst &parameters=
    function_type.parameters();

  for(code_typet::parameterst::iterator
      it=parameters.begin();
      it!=parameters.end();
      it++)
    convert_parameter(current_mode, *it);
}

void cpp_typecheckt::convert_function(symbolt &symbol)
{
  // Guard against recursive type-checking (e.g., constexpr functions
  // that call themselves).
  if(functions_being_typechecked.count(symbol.name))
    return;
  functions_being_typechecked.insert(symbol.name);

  code_typet &function_type=
    to_code_type(template_subtype(symbol.type));

  // only a prototype?
  if(symbol.value.is_nil())
    return;

  if(symbol.value.id() != ID_code)
  {
    error().source_location = symbol.location;
    error() << "function '" << symbol.name << "' is initialized with "
            << symbol.value.id() << eom;
    throw 0;
  }

  // C++11 deleted functions: = delete
  if(to_code(symbol.value).get_statement() == ID_cpp_delete)
  {
    symbol.value.make_nil();
    return;
  }

  // enter appropriate scope
  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_scopet &function_scope=cpp_scopes.set_scope(symbol.name);

  // fix the scope's prefix
  function_scope.prefix=id2string(symbol.name)+"::";

  // For friend functions defined inside a class, add the class scope
  // as a secondary scope so that class-scope names are visible.
  const irep_idt &friend_class = symbol.type.get(ID_C_class);
  if(!friend_class.empty())
  {
    auto it = cpp_scopes.id_map.find(friend_class);
    if(it != cpp_scopes.id_map.end())
      function_scope.add_secondary_scope(
        static_cast<cpp_scopet &>(*it->second));
  }

  // genuine function definition -- do the parameter declarations
  convert_parameters(symbol.mode, function_type);

  // create "this" if it's a non-static method
  if(function_scope.is_method &&
     !function_scope.is_static_member)
  {
    code_typet::parameterst &parameters=function_type.parameters();
    DATA_INVARIANT(parameters.size() >= 1, "parameters expected");
    code_typet::parametert &this_parameter_expr=parameters.front();
    function_scope.this_expr = symbol_exprt{
      this_parameter_expr.get_identifier(), this_parameter_expr.type()};
  }
  else
    function_scope.this_expr.make_nil();

  // if it is a destructor, add the implicit code
  if(to_code_type(symbol.type).return_type().id() == ID_destructor)
  {
    const symbolt &msymb = lookup(symbol.type.get(ID_C_member_name));

    PRECONDITION(symbol.value.id() == ID_code);
    PRECONDITION(symbol.value.get(ID_statement) == ID_block);

    // Skip adding destructor code for virtual function thunks — the
    // thunk just calls the real destructor which already has the code.
    const auto &this_param_type =
      to_pointer_type(function_type.parameters().front().type());
    bool is_thunk =
      this_param_type.base_type().get(ID_identifier) != msymb.name;

    if(
      !is_thunk &&
      (!symbol.value.has_operands() ||
       !to_multi_ary_expr(symbol.value).op0().has_operands() ||
       to_multi_ary_expr(to_multi_ary_expr(symbol.value).op0()).op0().id() !=
         ID_already_typechecked))
    {
      symbol.value.copy_to_operands(
        dtor(msymb, to_symbol_expr(function_scope.this_expr)));
    }
  }

  // do the function body
  // Save and restore break/continue/case flags, because convert_function
  // may be called recursively (e.g., during constexpr evaluation or
  // template instantiation triggered by type-checking an expression
  // inside another function body).
  bool old_break_is_allowed = break_is_allowed;
  bool old_continue_is_allowed = continue_is_allowed;
  bool old_case_is_allowed = case_is_allowed;
  start_typecheck_code();

  // save current return type
  typet old_return_type=return_type;

  return_type=function_type.return_type();

  // constructor, destructor?
  if(return_type.id() == ID_constructor || return_type.id() == ID_destructor)
    return_type = void_type();

  // C++14: auto return type deduction
  bool defer_auto_return = false;
  if(has_auto(return_type))
  {
    // Find the first return statement and deduce the type.
    // If the body contains if constexpr, the return expression may be
    // in a discarded branch and fail to type-check. In that case,
    // defer deduction to after body type-checking.
    std::function<const exprt *(const codet &)> find_return =
      [&](const codet &code) -> const exprt *
    {
      if(code.get_statement() == ID_return)
      {
        const auto &ret = to_code_frontend_return(code);
        if(ret.has_return_value())
          return &ret.return_value();
      }
      for(const auto &op : code.operands())
      {
        if(op.id() == ID_code)
        {
          const exprt *r = find_return(to_code(op));
          if(r != nullptr)
            return r;
        }
      }
      return nullptr;
    };

    const exprt *ret_expr = find_return(to_code(symbol.value));
    if(ret_expr != nullptr)
    {
      const std::size_t saved_errors =
        get_message_handler().get_message_count(messaget::M_ERROR);
      const unsigned saved_verbosity = get_message_handler().get_verbosity();
      get_message_handler().set_verbosity(0);

      try
      {
        exprt tmp = *ret_expr;
        typecheck_expr(tmp);
        typet deduced = tmp.type();
        // C++14 decltype(auto): if the return expression is a
        // parenthesized lvalue, deduce a reference type
        if(
          return_type.id() == ID_decltype && return_type.get_bool("#auto") &&
          tmp.get_bool(ID_C_lvalue))
        {
          deduced = reference_typet(deduced, config.ansi_c.pointer_width);
        }
        cpp_convert_auto(
          function_type.return_type(), deduced, get_message_handler());
        typecheck_type(function_type.return_type());
        return_type = function_type.return_type();
      }
      catch(...)
      {
        // Return expression failed to type-check (likely in a discarded
        // if constexpr branch). Defer deduction to after body type-checking.
        get_message_handler().set_message_count(
          messaget::M_ERROR, saved_errors);
        defer_auto_return = true;
      }

      get_message_handler().set_verbosity(saved_verbosity);
    }
    else
    {
      // No return statement — deduce void
      function_type.return_type() = void_type();
      return_type = void_type();
    }
  }

  // C++20: generate body for defaulted operator<=>
  if(
    symbol.base_name == "operator<=>" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    const irep_idt &class_id = symbol.type.get(ID_C_member_name);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      // Find the parameter name (second param after this)
      irep_idt arg_name;
      if(fn_params.size() >= 2)
        arg_name = fn_params[1].get_base_name();
      if(arg_name.empty())
        arg_name = "#anon_arg0";

      source_locationt loc = symbol.location;
      code_blockt body;
      body.add_source_location() = loc;

      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.type().id() == ID_code)
          continue;
        if(c.get_base_name() == "@most_derived")
          continue;

        const irep_idt &mem = c.get_base_name();
        cpp_namet lhs(mem, loc);
        exprt rhs(ID_member);
        rhs.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs.copy_to_operands(cpp_namet(arg_name, loc).as_expr());
        rhs.add_source_location() = loc;

        typet int_type = signed_int_type();
        binary_relation_exprt lt(lhs.as_expr(), ID_lt, rhs);
        lt.add_source_location() = loc;
        binary_relation_exprt gt(lhs.as_expr(), ID_gt, rhs);
        gt.add_source_location() = loc;
        if_exprt inner(
          std::move(gt), from_integer(1, int_type), from_integer(0, int_type));
        inner.add_source_location() = loc;
        if_exprt cmp(
          std::move(lt), from_integer(-1, int_type), std::move(inner));
        cmp.add_source_location() = loc;

        notequal_exprt ne(cmp, from_integer(0, int_type));
        ne.add_source_location() = loc;
        code_frontend_returnt ret(cmp);
        ret.add_source_location() = loc;
        code_ifthenelset ifs(std::move(ne), std::move(ret));
        ifs.add_source_location() = loc;
        body.add(std::move(ifs));
      }

      code_frontend_returnt ret0(from_integer(0, signed_int_type()));
      ret0.add_source_location() = loc;
      body.add(std::move(ret0));

      symbol.value = std::move(body);
    }
  }

  // C++20: generate body for defaulted operator==
  if(
    symbol.base_name == "operator==" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    const irep_idt &class_id = symbol.type.get(ID_C_member_name);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      irep_idt arg_name;
      if(fn_params.size() >= 2)
        arg_name = fn_params[1].get_base_name();
      if(arg_name.empty())
        arg_name = "#anon_arg0";

      source_locationt loc = symbol.location;

      // Build conjunction: m1==rhs.m1 && m2==rhs.m2 && ...
      exprt result = true_exprt();
      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.type().id() == ID_code)
          continue;
        if(c.get_base_name() == "@most_derived")
          continue;

        const irep_idt &mem = c.get_base_name();
        cpp_namet lhs(mem, loc);
        exprt rhs(ID_member);
        rhs.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs.copy_to_operands(cpp_namet(arg_name, loc).as_expr());
        rhs.add_source_location() = loc;

        equal_exprt eq(lhs.as_expr(), rhs);
        eq.add_source_location() = loc;

        if(result.is_true())
          result = std::move(eq);
        else
        {
          and_exprt conj(std::move(result), std::move(eq));
          conj.add_source_location() = loc;
          result = std::move(conj);
        }
      }

      code_blockt body;
      body.add_source_location() = loc;
      code_frontend_returnt ret(std::move(result));
      ret.add_source_location() = loc;
      body.add(std::move(ret));

      symbol.value = std::move(body);
    }
  }

  // C++20: generate body for defaulted operator!=
  if(
    symbol.base_name == "operator!=" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    const irep_idt &class_id = symbol.type.get(ID_C_member_name);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      irep_idt arg_name;
      if(fn_params.size() >= 2)
        arg_name = fn_params[1].get_base_name();
      if(arg_name.empty())
        arg_name = "#anon_arg0";

      source_locationt loc = symbol.location;

      // Build: !(m1==rhs.m1 && m2==rhs.m2 && ...)
      exprt eq_result = true_exprt();
      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.type().id() == ID_code)
          continue;
        if(c.get_base_name() == "@most_derived")
          continue;

        const irep_idt &mem = c.get_base_name();
        cpp_namet lhs(mem, loc);
        exprt rhs(ID_member);
        rhs.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs.copy_to_operands(cpp_namet(arg_name, loc).as_expr());
        rhs.add_source_location() = loc;

        equal_exprt eq(lhs.as_expr(), rhs);
        eq.add_source_location() = loc;

        if(eq_result.is_true())
          eq_result = std::move(eq);
        else
        {
          and_exprt conj(std::move(eq_result), std::move(eq));
          conj.add_source_location() = loc;
          eq_result = std::move(conj);
        }
      }

      not_exprt neg(std::move(eq_result));
      neg.add_source_location() = loc;

      code_blockt body;
      body.add_source_location() = loc;
      code_frontend_returnt ret(std::move(neg));
      ret.add_source_location() = loc;
      body.add(std::move(ret));

      symbol.value = std::move(body);
    }
  }

  typecheck_code(to_code(symbol.value));

  // Deferred auto return type deduction: the initial attempt failed
  // (e.g., if constexpr with type-dependent discarded branch).
  // Now that the body is type-checked, find a return statement in the
  // surviving branches.
  if(defer_auto_return)
  {
    std::function<const typet *(const codet &)> find_return_type =
      [&](const codet &code) -> const typet *
    {
      if(code.get_statement() == ID_return && code.operands().size() == 1)
      {
        return &code.op0().type();
      }
      for(const auto &op : code.operands())
      {
        if(op.id() == ID_code)
        {
          const typet *r = find_return_type(to_code(op));
          if(r != nullptr)
            return r;
        }
      }
      return nullptr;
    };

    const typet *deduced = find_return_type(to_code(symbol.value));
    if(deduced != nullptr)
    {
      function_type.return_type() = *deduced;
      return_type = *deduced;
    }
    else
    {
      function_type.return_type() = void_type();
      return_type = void_type();
    }
  }

  symbol.value.type()=symbol.type;

  return_type = old_return_type;
  break_is_allowed = old_break_is_allowed;
  continue_is_allowed = old_continue_is_allowed;
  case_is_allowed = old_case_is_allowed;

  deferred_typechecking.erase(symbol.name);
  functions_being_typechecked.erase(symbol.name);
}

/// for function overloading
irep_idt cpp_typecheckt::function_identifier(const typet &type)
{
  const code_typet &function_type=
    to_code_type(template_subtype(type));

  const code_typet::parameterst &parameters=
    function_type.parameters();

  std::string result;
  bool first=true;

  result+='(';

  // the name of the function should not depend on
  // the class name that is encoded in the type of this,
  // but we must distinguish "const" and "non-const" member
  // functions

  code_typet::parameterst::const_iterator it=
    parameters.begin();

  if(it != parameters.end() && it->get_this())
  {
    const typet &pointer=it->type();
    const typet &symbol = to_pointer_type(pointer).base_type();
    if(symbol.get_bool(ID_C_constant))
      result += "$const";
    if(symbol.get_bool(ID_C_volatile))
      result += "$volatile";
    result += id2string(ID_this);
    first=false;
    it++;
  }

  // we skipped the "this", on purpose!

  for(; it!=parameters.end(); it++)
  {
    if(first)
      first=false;
    else
      result+=',';
    typet tmp_type=it->type();
    // C/C++ function parameters of function type decay to
    // pointer-to-function.  Normalise here so that the identifier
    // is the same regardless of declaration style.
    if(tmp_type.id() == ID_code)
      tmp_type = pointer_type(tmp_type);
    // Top-level const/volatile on parameters does not affect the
    // function signature per [dcl.fct]/5.
    tmp_type.remove(ID_C_constant);
    tmp_type.remove(ID_C_volatile);
    result += cpp_type2name(tmp_type);
  }

  result+=')';

  return result;
}
