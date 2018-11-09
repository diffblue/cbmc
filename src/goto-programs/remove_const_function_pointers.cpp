/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// Goto Programs

#include "remove_const_function_pointers.h"

#include <util/arith_tools.h>
#include <util/format_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "goto_functions.h"

#define LOG(message, irep) \
  do { \
    debug().source_location = irep.source_location(); \
    debug() << message << ": " << format(irep) << eom; \
  } \
  while(0)

/// To take a function call on a function pointer, and if possible resolve it to
/// a small collection of possible values.
/// \param message_handler: The message handler for messaget
/// \param ns: The namespace to use to resolve types
/// \param symbol_table: The symbol table to look up symbols in
remove_const_function_pointerst::remove_const_function_pointerst(
  message_handlert &message_handler,
  const namespacet &ns,
  const symbol_tablet &symbol_table):
    messaget(message_handler),
    ns(ns),
    symbol_table(symbol_table)
{}

/// To take a function call on a function pointer, and if possible resolve it to
/// a small collection of possible values. It will resolve function pointers
/// that are const and: - assigned directly to a function - assigned to a value
/// in an array of functions - assigned to a const struct component Or
/// variations within.
/// \param base_expression: The function call through a function pointer
/// \param out_functions: The functions that (symbols of type ID_code) the base
/// expression could take.
/// \return Returns true if it was able to resolve the call, false if not. If it
///   returns true, out_functions will be populated by all the possible values
///   the function pointer could be.
bool remove_const_function_pointerst::operator()(
  const exprt &base_expression,
  functionst &out_functions)
{
  // Replace all const symbols with their values
  exprt non_symbol_expression=replace_const_symbols(base_expression);
  return try_resolve_function_call(non_symbol_expression, out_functions);
}

/// To collapse the symbols down to their values where possible This takes a
/// very general approach, recreating the expr tree exactly as it was and
/// ignoring what type of expressions are found and instead recurses over all
/// the operands.
/// \param expression: The expression to resolve symbols in
/// \return Returns a modified version of the expression, with all const symbols
///   resolved to their actual values.
exprt remove_const_function_pointerst::replace_const_symbols(
  const exprt &expression) const
{
  if(expression.id()==ID_symbol)
  {
    if(is_const_expression(expression))
    {
      const symbolt &symbol =
        *symbol_table.lookup(to_symbol_expr(expression).get_identifier());
      if(symbol.type.id()!=ID_code)
      {
        const exprt &symbol_value=symbol.value;
        return replace_const_symbols(symbol_value);
      }
      else
      {
        return expression;
      }
    }
    else
    {
      return expression;
    }
  }
  else
  {
    exprt const_symbol_cleared_expr=expression;
    const_symbol_cleared_expr.operands().clear();
    for(const exprt &op : expression.operands())
    {
      exprt const_symbol_cleared_op=replace_const_symbols(op);
      const_symbol_cleared_expr.operands().push_back(const_symbol_cleared_op);
    }

    return const_symbol_cleared_expr;
  }
}

/// Look up a symbol in the symbol table and return its value
/// \param symbol_expr: The symbol expression
/// \return The expression value of the symbol.
exprt remove_const_function_pointerst::resolve_symbol(
  const symbol_exprt &symbol_expr) const
{
  const symbolt &symbol=
    *symbol_table.lookup(symbol_expr.get_identifier());
  return symbol.value;
}

/// To resolve an expression to the specific function calls it can be. This is
/// different to try_resolve_expression which isn't explicitly looking for
/// functions and is instead just trying to squash particular exprt structures.
/// \param expr: The expression to get the possible function calls
/// \param out_functions: The functions this expression could be resolved to
/// \return Returns true if it was able to resolve the expression to some
///   specific functions. If this is the case, out_functions will contain the
///   possible functions.
bool remove_const_function_pointerst::try_resolve_function_call(
  const exprt &expr, functionst &out_functions)
{
  PRECONDITION(out_functions.empty());
  const exprt &simplified_expr=simplify_expr(expr, ns);
  bool resolved=false;
  functionst resolved_functions;
  if(simplified_expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(simplified_expr);
    resolved=try_resolve_index_of_function_call(index_expr, resolved_functions);
  }
  else if(simplified_expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(simplified_expr);
    resolved=try_resolve_member_function_call(member_expr, resolved_functions);
  }
  else if(simplified_expr.id()==ID_address_of)
  {
    address_of_exprt address_expr=to_address_of_expr(simplified_expr);
    resolved=try_resolve_address_of_function_call(
      address_expr, resolved_functions);
  }
  else if(simplified_expr.id()==ID_dereference)
  {
    const dereference_exprt &deref=to_dereference_expr(simplified_expr);
    resolved=try_resolve_dereference_function_call(deref, resolved_functions);
  }
  else if(simplified_expr.id()==ID_typecast)
  {
    typecast_exprt typecast_expr=to_typecast_expr(simplified_expr);
    resolved=
      try_resolve_typecast_function_call(typecast_expr, resolved_functions);
  }
  else if(simplified_expr.id()==ID_symbol)
  {
    if(simplified_expr.type().id()==ID_code)
    {
      resolved_functions.insert(to_symbol_expr(simplified_expr));
      resolved=true;
    }
    else
    {
      LOG("Non const symbol wasn't squashed", simplified_expr);
      resolved=false;
    }
  }
  else if(simplified_expr.id()==ID_constant)
  {
    if(simplified_expr.is_zero())
    {
      // We have the null pointer - no need to throw everything away
      // but we don't add any functions either
      resolved=true;
    }
    else
    {
      LOG("Non-zero constant value found", simplified_expr);
      resolved=false;
    }
  }
  else
  {
    LOG("Unrecognised expression", simplified_expr);
    resolved=false;
  }

  if(resolved)
  {
    out_functions.insert(resolved_functions.begin(), resolved_functions.end());
    return true;
  }
  else
  {
    return false;
  }
}

/// To resolve a collection of expressions to the specific function calls they
/// can be. Returns a collection if and only if all of them can be resolved.
/// \param exprs: The expressions to evaluate
/// \param out_functions: The functions these expressions resolve to
/// \return Returns true if able to resolve each of the expressions down to one
///   or more functions.
bool remove_const_function_pointerst::try_resolve_function_calls(
  const expressionst &exprs, functionst &out_functions)
{
  for(const exprt &value : exprs)
  {
    functionst potential_out_functions;
    bool resolved_value=
      try_resolve_function_call(value, potential_out_functions);

    if(resolved_value)
    {
      out_functions.insert(
        potential_out_functions.begin(),
        potential_out_functions.end());
    }
    else
    {
      LOG("Could not resolve expression in array", value);
      return false;
    }
  }
  return true;
}

/// To resolve an expression to the specific function calls it can be.
/// Specifically, this function deals with index expressions where it squashes
/// its array and squash its index If we can get a precise number for the index,
/// we try_resolve_function_call on its value otherwise
/// try_resolve_function_call on each and return the union of them all
/// \param index_expr: The index expression to resolve to possible function
///   calls
/// \param out_functions: The functions this expression could be
/// \return Returns true if it was able to resolve the index expression to some
///   specific functions. If this is the case, out_functions will contain the
///   possible functions.
bool remove_const_function_pointerst::try_resolve_index_of_function_call(
  const index_exprt &index_expr, functionst &out_functions)
{
  expressionst potential_array_values;
  bool array_const;
  bool resolved=
    try_resolve_index_of(index_expr, potential_array_values, array_const);

  if(!resolved)
  {
    LOG("Could not resolve array", index_expr);
    return false;
  }

  if(!array_const)
  {
    LOG("Array not const", index_expr);
    return false;
  }

  return try_resolve_function_calls(potential_array_values, out_functions);
}

/// To resolve an expression to the specific function calls it can be.
/// Specifically, this function deals with member expressions by using
/// try_resolve_member and then recursing on its value.
/// \param member_expr: The member expression to resolve to possible function
///   calls
/// \param out_functions: The functions this expression could be
/// \return Returns true if it was able to resolve the member expression to some
///   specific functions. If this is the case, out_functions will contain the
///   possible functions.
bool remove_const_function_pointerst::try_resolve_member_function_call(
  const member_exprt &member_expr, functionst &out_functions)
{
  expressionst potential_component_values;
  bool struct_const;
  bool resolved=
    try_resolve_member(member_expr, potential_component_values, struct_const);

  if(!resolved)
  {
    LOG("Could not resolve struct", member_expr);
    return false;
  }

  if(!struct_const)
  {
    LOG("Struct was not const so can't resolve values on it", member_expr);
    return false;
  }

  return try_resolve_function_calls(potential_component_values, out_functions);
}

/// To resolve an expression to the specific function calls it can be.
/// Specifically, this function deals with address_of expressions.
/// \param address_expr: The address_of expression to resolve to possible
///   function calls
/// \param out_functions: The functions this expression could be
/// \return Returns true if it was able to resolve the address_of expression to
///   some specific functions. If this is the case, out_functions will contain
///   the possible functions.
bool remove_const_function_pointerst::try_resolve_address_of_function_call(
  const address_of_exprt &address_expr, functionst &out_functions)
{
  bool resolved=
    try_resolve_function_call(address_expr.object(), out_functions);
  if(!resolved)
  {
    LOG("Failed to resolve address of", address_expr);
  }
  return resolved;
}

/// To resolve an expression to the specific function calls it can be.
/// Specifically, this function deals with dereference expressions by using
/// try_resolve_dereferebce and then recursing on its value.
/// \param deref_expr: The dereference expression to resolve to possible
///   function calls
/// \param out_functions: The functions this expression could be
/// \return Returns true if it was able to resolve the dereference expression to
///   some specific functions. If this is the case, out_functions will contain
///   the possible functions.
bool remove_const_function_pointerst::try_resolve_dereference_function_call(
  const dereference_exprt &deref_expr, functionst &out_functions)
{
  expressionst potential_deref_values;
  bool deref_const;
  bool resolved=
    try_resolve_dereference(deref_expr, potential_deref_values, deref_const);

  if(!resolved)
  {
    LOG("Failed to squash dereference", deref_expr);
    return false;
  }

  if(!deref_const)
  {
    LOG("Dereferenced value was not const so can't dereference", deref_expr);
    return false;
  }

  return try_resolve_function_calls(potential_deref_values, out_functions);
}

/// To resolve an expression to the specific function calls it can be.
/// Specifically, this function deals with typecast expressions by looking at
/// the type cast values.
/// \param typecast_expr: The typecast expression to resolve to possible
///   function calls
/// \param out_functions: The functions this expression could be
/// \return Returns true if it was able to resolve the typecast expression to
///   some specific functions. If this is the case, out_functions will contain
///   the possible functions.
bool remove_const_function_pointerst::try_resolve_typecast_function_call(
  const typecast_exprt &typecast_expr, functionst &out_functions)
{
  // We simply ignore typecasts and assume they are valid
  // I thought simplify_expr would deal with this, but for example
  // a cast from a 32 bit width int to a 64bit width int it doesn't seem
  // to allow
  functionst typecast_values;
  bool resolved=
    try_resolve_function_call(typecast_expr.op(), typecast_values);

  if(resolved)
  {
    out_functions.insert(typecast_values.begin(), typecast_values.end());
    return true;
  }
  else
  {
    LOG("Failed to squash typecast", typecast_expr);
    return false;
  }
}

/// To squash various expr types to simplify the expression. ID_index -> dig to
/// find ID_array and get the values out of it ID_member -> dig to find
/// ID_struct and extract the component value ID_dereference -> dig to find
/// ID_address_of and extract the value ID_typecast -> return the value
/// ID_symbol -> return false, const symbols are squashed first and non const
/// symbols cannot be squashed Everything else -> unchanged
/// \param expr: The expression to try and squash
/// \param out_resolved_expression: The squashed version of this expression
/// \param out_is_const: Is the squashed expression constant
/// \return Returns true providing the squashing went OK (note it may not have
///   squashed anything). The out_resolved_expression will in this case be all
///   the possible squashed versions of the supplied expression. The
///   out_is_const will return whether the squashed value is suitably const
///   (e.g. if we squashed a struct access, was the struct const).
bool remove_const_function_pointerst::try_resolve_expression(
  const exprt &expr, expressionst &out_resolved_expression, bool &out_is_const)
{
  exprt simplified_expr=simplify_expr(expr, ns);
  bool resolved;
  expressionst resolved_expressions;
  bool is_resolved_expression_const = false;
  if(simplified_expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(simplified_expr);
    resolved=
      try_resolve_index_of(
        index_expr, resolved_expressions, is_resolved_expression_const);
  }
  else if(simplified_expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(simplified_expr);
    resolved=try_resolve_member(
      member_expr, resolved_expressions, is_resolved_expression_const);
  }
  else if(simplified_expr.id()==ID_dereference)
  {
    const dereference_exprt &deref=to_dereference_expr(simplified_expr);
    resolved=
      try_resolve_dereference(
        deref, resolved_expressions, is_resolved_expression_const);
  }
  else if(simplified_expr.id()==ID_typecast)
  {
    typecast_exprt typecast_expr=to_typecast_expr(simplified_expr);
    resolved=
      try_resolve_typecast(
        typecast_expr, resolved_expressions, is_resolved_expression_const);
  }
  else if(simplified_expr.id()==ID_symbol)
  {
    LOG("Non const symbol will not be squashed", simplified_expr);
    resolved=false;
  }
  else
  {
    resolved_expressions.push_back(simplified_expr);
    is_resolved_expression_const=is_const_expression(simplified_expr);
    resolved=true;
  }

  if(resolved)
  {
    out_resolved_expression.insert(
      out_resolved_expression.end(),
      resolved_expressions.begin(),
      resolved_expressions.end());
    out_is_const=is_resolved_expression_const;
    return true;
  }
  else
  {
    return false;
  }
}

/// Given an index into an array, resolve, if possible, the index that is being
/// accessed. This deals with symbols and typecasts to constant values.
/// \param expr: The expression of the index of the index expression (e.g.
///   index_exprt::index())
/// \param out_array_index: The constant value the index takes
/// \return Returns true if was able to find a constant value for the index
///   expression. If true, then out_array_index will be the index within the
///   array that the function pointer is pointing to.
bool remove_const_function_pointerst::try_resolve_index_value(
  const exprt &expr, mp_integer &out_array_index)
{
  expressionst index_value_expressions;
  bool is_const=false;
  bool resolved=try_resolve_expression(expr, index_value_expressions, is_const);
  if(resolved)
  {
    if(index_value_expressions.size()==1 &&
       index_value_expressions.front().id()==ID_constant)
    {
      const constant_exprt &constant_expr=
        to_constant_expr(index_value_expressions.front());
      mp_integer array_index;
      bool errors=to_integer(constant_expr, array_index);
      if(!errors)
      {
        out_array_index=array_index;
      }
      return !errors;
    }
    else
    {
      return false;
    }
  }
  else
  {
    return false;
  }
}

/// To squash an index access by first finding the array it is accessing Then if
/// the index can be resolved, return the squashed value. If the index can't be
/// determined then squash each value in the array and return them all.
/// \param index_expr: The index expression to  to resolve
/// \param out_expressions: The expressions this expression could be
/// \param out_is_const: Is the squashed expression constant
/// \return Returns true if it was able to squash the index expression If this
///   is the case, out_expressions will contain the possible values this
///   index_of could return The out_is_const will return whether either the
///   array itself is const, or the values of the array are const.
bool remove_const_function_pointerst::try_resolve_index_of(
  const index_exprt &index_expr,
  expressionst &out_expressions,
  bool &out_is_const)
{
  // Get the array(s) it belongs to
  expressionst potential_array_exprs;
  bool array_const=false;
  bool resolved_array=
    try_resolve_expression(
      index_expr.array(),
      potential_array_exprs,
      array_const);

  if(resolved_array)
  {
    bool all_possible_const=true;
    for(const exprt &potential_array_expr : potential_array_exprs)
    {
      all_possible_const=
        all_possible_const &&
        is_const_type(potential_array_expr.type().subtype());

      if(potential_array_expr.id()==ID_array)
      {
        // Get the index if we can
        mp_integer value;
        if(try_resolve_index_value(index_expr.index(), value))
        {
          expressionst array_out_functions;
          const exprt &func_expr =
            potential_array_expr.operands()[numeric_cast_v<std::size_t>(value)];
          bool value_const=false;
          bool resolved_value=
            try_resolve_expression(func_expr, array_out_functions, value_const);

          if(resolved_value)
          {
            out_expressions.insert(
              out_expressions.end(),
              array_out_functions.begin(),
              array_out_functions.end());
          }
          else
          {
            LOG("Failed to resolve array value", func_expr);
            return false;
          }
        }
        else
        {
          // We don't know what index it is,
          // but we know the value is from the array
          for(const exprt &array_entry : potential_array_expr.operands())
          {
            expressionst array_contents;
            bool is_entry_const;
            bool resolved_value=
              try_resolve_expression(
                array_entry, array_contents, is_entry_const);

            if(!resolved_value)
            {
              LOG("Failed to resolve array value", array_entry);
              return false;
            }

            for(const exprt &resolved_array_entry : array_contents)
            {
              out_expressions.push_back(resolved_array_entry);
            }
          }
        }
      }
      else
      {
        LOG(
          "Squashing index of did not result in an array",
          potential_array_expr);
        return false;
      }
    }

    out_is_const=all_possible_const || array_const;
    return true;
  }
  else
  {
    LOG("Failed to squash index of to array expression", index_expr);
    return false;
  }
}

/// To squash an member access by first finding the struct it is accessing Then
/// return the squashed value of the relevant component.
/// \param member_expr: The member expression to resolve.
/// \param out_expressions: The expressions this component could be
/// \param out_is_const: Is the squashed expression constant
/// \return Returns true if it was able to squash the member expression If this
///   is the case, out_expressions will contain the possible values this member
///   could return The out_is_const will return whether the struct is const.
bool remove_const_function_pointerst::try_resolve_member(
  const member_exprt &member_expr,
  expressionst &out_expressions,
  bool &out_is_const)
{
  expressionst potential_structs;
  bool is_struct_const;

  // Get the struct it belongs to
  bool resolved_struct=
    try_resolve_expression(
      member_expr.compound(), potential_structs, is_struct_const);
  if(resolved_struct)
  {
    for(const exprt &potential_struct : potential_structs)
    {
      if(potential_struct.id()==ID_struct)
      {
        struct_exprt struct_expr=to_struct_expr(potential_struct);
        const exprt &component_value=
          get_component_value(struct_expr, member_expr);
        expressionst resolved_expressions;
        bool component_const=false;
        bool resolved=
          try_resolve_expression(
            component_value, resolved_expressions, component_const);
        if(resolved)
        {
          out_expressions.insert(
            out_expressions.end(),
            resolved_expressions.begin(),
            resolved_expressions.end());
        }
        else
        {
          LOG("Could not resolve component value", component_value);
          return false;
        }
      }
      else
      {
        LOG(
          "Squashing member access did not resolve in a struct",
          potential_struct);
        return false;
      }
    }
    out_is_const=is_struct_const;
    return true;
  }
  else
  {
    LOG("Failed to squash struct access", member_expr);
    return false;
  }
}

/// To squash a dereference access by first finding the address_of the
/// dereference is dereferencing. Then return the squashed value of the relevant
/// component.
/// \param deref_expr: The dereference expression to resolve.
/// \param out_expressions: The expressions this dereference could be
/// \param out_is_const: Is the squashed expression constant
/// \return Returns true if it was able to squash the dereference expression If
///   this is the case, out_expressions will contain the possible values this
///   dereference could return The out_is_const will return whether the object
///   that gets dereferenced is constant.
bool remove_const_function_pointerst::try_resolve_dereference(
  const dereference_exprt &deref_expr,
  expressionst &out_expressions,
  bool &out_is_const)
{
  // We had a pointer, we need to check both the pointer
  // type can't be changed, and what it what pointing to
  // can't be changed
  expressionst pointer_values;
  bool pointer_const;
  bool resolved=
    try_resolve_expression(deref_expr.pointer(), pointer_values, pointer_const);
  if(resolved && pointer_const)
  {
    bool all_objects_const=true;
    for(const exprt &pointer_val : pointer_values)
    {
      if(pointer_val.id()==ID_address_of)
      {
        address_of_exprt address_expr=to_address_of_expr(pointer_val);
        bool object_const=false;
        expressionst out_object_values;
        bool resolved=
          try_resolve_expression(
            address_expr.object(), out_object_values, object_const);

        if(resolved)
        {
          out_expressions.insert(
            out_expressions.end(),
            out_object_values.begin(),
            out_object_values.end());

          all_objects_const&=object_const;
        }
        else
        {
          LOG("Failed to resolve value of a dereference", address_expr);
        }
      }
      else
      {
        LOG(
          "Squashing dereference did not result in an address", pointer_val);
        return false;
      }
    }
    out_is_const=all_objects_const;
    return true;
  }
  else
  {
    if(!resolved)
    {
      LOG("Failed to resolve pointer of dereference", deref_expr);
    }
    else if(!pointer_const)
    {
      LOG("Pointer value not const so can't squash", deref_expr);
    }
    return false;
  }
}

/// To squash a typecast access.
/// \param typecast_expr: The typecast expression to resolve.
/// \param out_expressions: The expressions this typecast could be
/// \param out_is_const: Is the squashed expression constant
/// \return Returns true if it was able to squash the typecast expression If
///   this is the case, out_expressions will contain the possible values after
///   removing the typecast.
bool remove_const_function_pointerst::try_resolve_typecast(
  const typecast_exprt &typecast_expr,
  expressionst &out_expressions,
  bool &out_is_const)
{
  expressionst typecast_values;
  bool typecast_const;
  bool resolved=
    try_resolve_expression(
      typecast_expr.op(), typecast_values, typecast_const);

  if(resolved)
  {
    out_expressions.insert(
      out_expressions.end(),
      typecast_values.begin(),
      typecast_values.end());
    out_is_const=typecast_const;
    return true;
  }
  else
  {
    LOG("Could not resolve typecast value", typecast_expr);
    return false;
  }
}

/// To evaluate the const-ness of the expression type.
/// \param expression: The expression to check
/// \return Returns true if the type of the expression is constant.
bool remove_const_function_pointerst::is_const_expression(
  const exprt &expression) const
{
  return is_const_type(expression.type());
}

/// To evaluate the const-ness of the type.
/// \param type: The type to check
/// \return Returns true if the type has ID_C_constant or is an array since
///   arrays are implicitly const in C.
bool remove_const_function_pointerst::is_const_type(const typet &type) const
{
  if(type.id() == ID_array && type.subtype().get_bool(ID_C_constant))
    return true;

  return type.get_bool(ID_C_constant);
}

/// To extract the value of the specific component within a struct
/// \param struct_expr: The expression of the structure being accessed
/// \param member_expr: The expression saying which component is being accessed
/// \return Returns the value of a specific component for a given struct
///   expression.
exprt remove_const_function_pointerst::get_component_value(
  const struct_exprt &struct_expr, const member_exprt &member_expr)
{
  const struct_typet &struct_type=to_struct_type(ns.follow(struct_expr.type()));
  size_t component_number=
    struct_type.component_number(member_expr.get_component_name());

  return struct_expr.operands()[component_number];
}
