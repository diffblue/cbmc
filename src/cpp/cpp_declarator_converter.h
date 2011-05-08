/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_DECLARATOR_CONVERTER_H
#define CPROVER_CPP_DECLARATOR_CONVERTER_H

#include <symbol.h>

#include "cpp_declarator.h"
#include "cpp_declaration.h"
#include "cpp_scope.h"

// converts a cpp_declator plus some
// additional information stored in the class
// into a symbol

class cpp_declarator_convertert
{
public:
  cpp_declarator_convertert(
    class cpp_typecheckt &_cpp_typecheck);

  bool is_typedef;
  bool is_template;
  bool is_template_argument;
  bool is_friend;
  irep_idt mode;

  symbolt &convert(
    const typet &type, // already typechecked
    const cpp_storage_spect &storage_spec,
    const cpp_member_spect &member_spec,
    cpp_declaratort &declarator);

  symbolt &convert(
    const cpp_declarationt &declaration,
    cpp_declaratort &declarator)
  {
    return convert(
      declaration.type(),
      declaration.storage_spec(),
      declaration.member_spec(),
      declarator);
  }

  class cpp_typecheckt &cpp_typecheck;

protected:
  std::string base_name;
  typet final_type;
  cpp_scopet *scope;
  irep_idt final_identifier;
  bool is_code;

  void get_final_identifier();
  irep_idt get_pretty_name();

  symbolt &convert_new_symbol(
    const cpp_storage_spect &storage_spec,
    const cpp_member_spect &member_spec,
    cpp_declaratort &declarator);

  void handle_initializer(
    symbolt &symbol,
    cpp_declaratort &declarator);

  void operator_overloading_rules(const symbolt &symbol);
  void main_function_rules(const symbolt &symbol);

  void enforce_rules(const symbolt &symbol);

  void check_array_types(
    typet &type,
    bool force_constant);

  bool is_code_type(const typet &type) const
  {
    return type.id()==ID_code ||
           (type.id()==ID_template && type.subtype().id()==ID_code);
  }

  void combine_types(
    const locationt &location,
    const typet &decl_type,
    symbolt &symbol);
};

#endif
