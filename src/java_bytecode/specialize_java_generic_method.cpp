/*******************************************************************\

Module: Generate Java Generic Method - Instantiate a generic method
        with concrete type information.

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include "specialize_java_generic_method.h"
#include "generate_java_generic_type.h"
#include <java_bytecode/java_types.h>
#include <util/expr_iterator.h>
#include <iostream>
#include <util/namespace.h>

specialize_java_generic_methodt::specialize_java_generic_methodt(
  message_handlert &message_handler):
    instantiate_generic_type(message_handler)
{}

/// Generate a copy of a given generic method, specialized with
/// the given concrete types and insert the method into the symbol
/// table.
/// \param generic_method The generic method to be specialized.
/// \param concrete_types A map from generic type variables to concrete types
/// with which to instantiate the generic method.
/// \param symbol_table The symbol table into which the generated method will
/// be inserted.
/// \return The symbol that was inserting into the symbol_table, or the existing
/// symbol if the method has already been specialized.
const symbolt& specialize_java_generic_methodt::operator()(
  const symbolt &generic_method,
  const type_variable_instantiationst &concrete_types,
  symbol_tablet &symbol_table) const
{
  INVARIANT(generic_method.type.id()==ID_code, "Only code symbols");
  INVARIANT(concrete_types.size()>0, "Should be at least one concrete type");
  // Another invariant is that concrete_types.size() > the total number of
  // type variables used in the method. However, determining that essentially
  // means iterating through the whole method structure and duplicating a
  // large chunk of the work we're about to do...


  // We need to decorate the signature of the specialized method to
  // differentiate the symbols of the generic method and the specialized
  // method. There's a design decision to be made here - do we actually modify
  // the java signature, or do we decorate it with additional
  // qualifiers. We are taking the approach of adding decorations because
  // that avoids the situation where the user may have already
  // declared an overloaded method that might have the same signature
  // as the specialized method we are about to create. By decorating the
  // existing symbol, we ensure that no legal Java program could have already
  // defined the symbol.
  const std::string& signature_decoration=
    instantiation_decoration(concrete_types);

  // Check the method has not already been specialized
  const symbolt *already_specialized=
    symbol_table.lookup(id2string(generic_method.name)+signature_decoration);
  if(already_specialized)
    return *already_specialized;

  // Convert concrete types into a map for faster lookups
  type_variable_instantiation_mapt concrete_type_map(concrete_types);

  // Copy the generic method as a starting point for the specialization
  symbolt specialized_method=generic_method;
  code_typet &specialized_code=to_code_type(specialized_method.type);

  // Handle a generic return type
  typet &method_return_type=specialized_code.return_type();
  instantiate_generic_types(
    method_return_type,
    concrete_type_map,
    symbol_table);

  // Set the name of the specialized method, but ensure we remember the
  // original method name because we need it for cleaning up internal symbol
  // names...
  const irep_idt original_name=specialized_method.name;
  specialized_method.name=
    id2string(specialized_method.name)+signature_decoration;

  for(code_typet::parametert &parameter : specialized_code.parameters())
  {
    typet &parameter_type=parameter.type();
    instantiate_generic_types(parameter_type, concrete_type_map, symbol_table);

    // Update the symbol name of the parameter to match the newly decorated
    // name of the specialized method.
    decorate_identifier(parameter, ID_C_identifier, original_name,
      signature_decoration);
  }

  // Updated the body of the specialized method so that all generic types are
  // specialized and that all references to symbols inside the method body refer
  // to the specialized method and not the generic method.
  // FIXME: Probably also need to update references to class fields to point to
  // FIXME: the specialized class fields, rather than the generic class fields?
  auto body_iterator=specialized_method.value.depth_begin();
  const auto body_end=specialized_method.value.depth_end();

  while(body_iterator!=body_end)
  {
    if(body_iterator->id()==ID_symbol)
    {
      exprt &symbol_expr=body_iterator.mutate();
      typet &symbol_type=symbol_expr.type();
      instantiate_generic_types(symbol_type, concrete_type_map, symbol_table);

      // Update the symbol identifier if needed to match the specialized
      // method name.
      decorate_identifier(symbol_expr, ID_identifier, original_name,
        signature_decoration);
    }

    ++body_iterator;
  }

  if(symbol_table.add(specialized_method))
  {
    // We should never hit this because the first thing
    // we do before starting to specialize the method
    // is check that the proposed symbol name doesn't
    // already exist.
    throw unsupported_java_method_specialization_exceptiont(
      "specialized method symbol already exists");
  }

  return symbol_table.lookup_ref(specialized_method.name);
}


/// Given a mapping from generic type variables to concrete types, generate
/// a string suitable for decorating symbol names with.
/// \param concrete_types The mapping from type variables to concrete types
/// \return A string suitable for inserting into a java signature
///
/// As an example, if a mapping such as this (pseudo code...):
/// [ {T,java.lang.Integer}, {U,java.lang.Double} ] is passed in, the return
/// string would look like "<java.lang.Integer,java.lang,Double>"
const std::string specialize_java_generic_methodt::instantiation_decoration(
  type_variable_instantiationst concrete_types)
{
  std::ostringstream decorated_signature_buffer;
  decorated_signature_buffer << "<";
  bool first=true;
  for(auto &concrete_type_entry : concrete_types)
  {
    if(first)
      first=false;
    else
      decorated_signature_buffer << ",";

    decorated_signature_buffer <<
      concrete_type_entry.second.get(ID_identifier);
  }
  decorated_signature_buffer << ">";
  return decorated_signature_buffer.str();
}

/// Instantiate a generic type with concrete types using a supplied mapping
/// from type variable to concrete type.
/// \param generic_type The typet that should be modified and instantiated.
/// \param concrete_type_map The mapping from type variable to concrete types.
/// \param symbol_table The symbol table into which we may add concrete types.
void specialize_java_generic_methodt::instantiate_generic_types(
  typet &generic_type,
  const type_variable_instantiation_mapt &concrete_type_map,
  symbol_tablet &symbol_table) const
{
  if(is_java_generic_parameter(generic_type))
  {
    // Instantiate a generic type variable 'T'
    instantiate_java_generic_parameter(
      to_java_generic_parameter(generic_type),
      concrete_type_map,
      symbol_table);
  }
  else if(is_java_generic_type(generic_type))
  {
    // Instantiate a generic type, such as 'List<T>'
    instantiate_java_generic_type(
      to_java_generic_type(generic_type),
      concrete_type_map);
    // At this point we have concrete types substituted into the generic type
    // variables, but it's still a generic type. Now go ahead and instantiate
    // this parameterized generic type fully.
    const symbolt &concrete_type=instantiate_generic_type
      (to_java_generic_type(generic_type),
      symbol_table);
    generic_type=concrete_type.type;
  }
}

/// Instantiate a given java generic parameter using a supplied mapping from
/// type variable to concrete type.
/// \param generic_parameter The java_generic_parametert that should be
/// modified and instantiated.
/// \param concrete_types The mapping of type variables to concrete types.
void specialize_java_generic_methodt::instantiate_java_generic_parameter(
  java_generic_parametert &generic_parameter,
  const type_variable_instantiation_mapt &concrete_types,
  const symbol_tablet &symbol_table) const
{
  namespacet ns(symbol_table);

  INVARIANT(
    generic_parameter.id()==ID_pointer,
    "All generic parameters should be pointers in java");
  INVARIANT(
    ns.follow(generic_parameter.subtype()).id()==ID_struct,
    "All generic parameters should point to symbols");

  const symbol_typet &generic_type_variable=generic_parameter.type_variable();
  const auto &instantiation_type=
    concrete_types.find(generic_type_variable.get_identifier());

  if(instantiation_type==concrete_types.end())
  {
    // If we ever want/need to support partially instantiated types,
    // we'll probably want to just return here.
    throw unsupported_java_method_specialization_exceptiont(
      "No concrete type supplied for generic type variable in parameter");
  }
  generic_parameter.subtype()=instantiation_type->second;
  generic_parameter.remove(ID_C_java_generic_parameter);
  generic_parameter.remove(ID_type_variables);
}


/// Instantiate a given java generic type using a supplied mapping from type
/// variable to concrete type.
/// \param generic_type The java_generic_typet that should be modified and
/// instantiated.
/// \param concrete_types The mapping of type variables to concrete types.
void specialize_java_generic_methodt::instantiate_java_generic_type(
  java_generic_typet &generic_type,
  const type_variable_instantiation_mapt &concrete_types) const
{
  INVARIANT(
    generic_type.subtype().id()==ID_symbol,
    "All generic parameters should point to symbols");

  // Replace the generic parameters
  for(java_generic_parametert &generic_parameter :
    to_java_generic_type(generic_type).generic_type_variables())
  {
    if(!is_java_generic_inst_parameter(generic_parameter))
    {
      const symbol_typet &generic_type_variable=
        generic_parameter.type_variable();
      const auto &instantiation_type=
        concrete_types.find(generic_type_variable.get_identifier());

      if(instantiation_type==concrete_types.end())
      {
        // If we ever want/need to support partially instantiated types,
        // we'll probably want to just return here.
        throw unsupported_java_method_specialization_exceptiont(
          "no concrete type supplied for generic type parameter");
      }
      generic_parameter.subtype()=instantiation_type->second;
      generic_parameter.set(ID_C_java_generic_inst_parameter, true);
    }
  }
}

/// Decorate an identifier on a given expression if the existing identifier
/// matches a given pattern.
/// \param expr The expression whos identifier should be decorated
/// \param identifier The particular identifier that should be modified
/// \param pattern The pattern to match and be decorated
/// \param decoration The string to use as decoration
///
/// An example of the use of this function might be:
///    decorate_identifier(
///      symbol,
///      ID_identifier,
///      "java::array[boolean].clone:()Ljava/lang/Object;"
///      "<decoration>")
/// which when given a 'symbol' expression who's 'ID_identifier' looks like:
///   'java::array[boolean].clone:()Ljava/lang/Object;::this' would replace
/// the identifier with:
///   'java::array[boolean].clone:()Ljava/lang/Object;<decoration>::this'
/// If the given 'expr' parameter does not already contain an identifier
/// whos value begins with the given 'pattern' string, then no change will
/// be made.
void specialize_java_generic_methodt::decorate_identifier(
  irept &expr,
  const irep_idt &identifier,
  const irep_idt &pattern,
  const irep_idt &decoration)
{
  const std::string &expr_identifier=id2string(expr.get(identifier));
  const std::string &pattern_str=id2string(pattern);

  // Does the pattern match the existing identifier
  if(has_prefix(expr_identifier, pattern_str))
  {
    const std::string dec_str=id2string(decoration);
    const std::string tail_str=expr_identifier.substr(pattern_str.size());
    const std::string new_ident=pattern_str+dec_str+tail_str;

    expr.set(identifier, new_ident);
  }
}
