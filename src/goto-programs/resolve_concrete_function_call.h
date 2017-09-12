/*******************************************************************\

 Module: GOTO Program Utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Given a virtual function call on a specific class, find which implementation
/// needs to be used.

#ifndef CPROVER_GOTO_PROGRAMS_RESOLVE_CONCRETE_FUNCTION_CALL_H
#define CPROVER_GOTO_PROGRAMS_RESOLVE_CONCRETE_FUNCTION_CALL_H

#include <util/symbol_table.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <goto-programs/class_hierarchy.h>

class resolve_concrete_function_callt
{
public:
  explicit resolve_concrete_function_callt(const symbol_tablet &symbol_table);
  resolve_concrete_function_callt(
    const symbol_tablet &symbol_table, const class_hierarchyt &class_hierarchy);

  class concrete_function_callt
  {
  public:
    concrete_function_callt()
    {}

    concrete_function_callt(
      const irep_idt &class_id, const irep_idt &method_id):
        class_identifier(class_id),
        function_identifier(method_id)
    {}

    irep_idt get_virtual_method_name() const;

    irep_idt get_class_identifier() const
    {
      return class_identifier;
    }

    irep_idt get_function_identifier() const
    {
      return function_identifier;
    }

    bool is_valid() const;

  private:
    irep_idt class_identifier;
    irep_idt function_identifier;
  };

  concrete_function_callt operator()(
    const irep_idt &class_id, const irep_idt &component_name);

  static irep_idt build_virtual_method_name(
    const irep_idt &class_name, const irep_idt &component_method_name);

private:
  bool does_implementation_exist(
    const irep_idt &class_name,
    const irep_idt &component_method_name,
    const irep_idt &calling_class_name);

  class_hierarchyt class_hierarchy;
  const symbol_tablet &symbol_table;
};

#endif // CPROVER_GOTO_PROGRAMS_RESOLVE_CONCRETE_FUNCTION_CALL_H
