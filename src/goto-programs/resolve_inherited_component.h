/*******************************************************************\

Module: GOTO Program Utilities

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Given a class and a component (either field or method), find the closest
/// parent that defines that component.

#ifndef CPROVER_GOTO_PROGRAMS_RESOLVE_INHERITED_COMPONENT_H
#define CPROVER_GOTO_PROGRAMS_RESOLVE_INHERITED_COMPONENT_H

#include <util/irep.h>
#include <util/optional.h>

#include <functional>

class symbolt;
class symbol_tablet;

class resolve_inherited_componentt
{
public:
  explicit resolve_inherited_componentt(const symbol_tablet &symbol_table);

  class inherited_componentt
  {
  public:
    inherited_componentt(
      const irep_idt &class_id, const irep_idt &component_id):
        class_identifier(class_id),
        component_identifier(component_id)
    {}

    irep_idt get_full_component_identifier() const;

    irep_idt get_class_identifier() const
    {
      return class_identifier;
    }

  private:
    irep_idt class_identifier;
    irep_idt component_identifier;
  };

  optionalt<inherited_componentt> operator()(
    const irep_idt &class_id,
    const irep_idt &component_name,
    bool include_interfaces,
    std::function<bool(const symbolt &)> user_filter = [](const symbolt &) {
      return true;
    });

  static irep_idt build_full_component_identifier(
    const irep_idt &class_name, const irep_idt &component_name);

private:
  const symbol_tablet &symbol_table;
};

optionalt<resolve_inherited_componentt::inherited_componentt>
get_inherited_method_implementation(
  const irep_idt &call_basename,
  const irep_idt &classname,
  const symbol_tablet &symbol_table);

#endif // CPROVER_GOTO_PROGRAMS_RESOLVE_INHERITED_COMPONENT_H
