/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_OBJECT_FACTORY_PARAMETERS_H
#define CPROVER_ANSI_C_C_OBJECT_FACTORY_PARAMETERS_H

#include <util/object_factory_parameters.h>

struct c_object_factory_parameterst final : public object_factory_parameterst
{
  c_object_factory_parameterst()
  {
  }

  explicit c_object_factory_parameterst(const optionst &options)
    : object_factory_parameterst(options)
  {
  }
};

/// Parse the c object factory parameters from a given command line
/// \param cmdline: Command line
/// \param [out] options: The options object that will be updated
void parse_c_object_factory_options(const cmdlinet &cmdline, optionst &options);

#endif
