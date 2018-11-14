/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_OBJECT_FACTORY_PARAMETERS_H
#define CPROVER_ANSI_C_C_OBJECT_FACTORY_PARAMETERS_H

#include <map>
#include <set>
#include <util/object_factory_parameters.h>
#include <util/optional.h>
#include <util/options.h>

struct c_object_factory_parameterst final : public object_factory_parameterst
{
  c_object_factory_parameterst() = default;

  explicit c_object_factory_parameterst(const optionst &options)
    : object_factory_parameterst(options)
  {
  }

  bool should_be_treated_as_array(irep_idt id) const;
  bool is_array_size_parameter(irep_idt id) const;
  optionalt<irep_idt> get_associated_size_variable(irep_idt array_id) const;

  void set(const optionst &options) override;

  std::size_t max_dynamic_array_size = 2;

private:
  std::set<irep_idt> pointers_to_treat_as_array;
  std::set<irep_idt> variables_that_hold_array_sizes;
  std::map<irep_idt, irep_idt> array_name_to_associated_array_size_variable;
};

/// Parse the c object factory parameters from a given command line
/// \param cmdline Command line
/// \param [out] options The options object that will be updated
void parse_c_object_factory_options(const cmdlinet &cmdline, optionst &options);

#endif
