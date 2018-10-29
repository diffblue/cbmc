/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_PARAMETERS_H
#define CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_PARAMETERS_H

#include <util/object_factory_parameters.h>

struct java_object_factory_parameterst final : public object_factory_parameterst
{
  java_object_factory_parameterst()
  {
  }

  explicit java_object_factory_parameterst(const optionst &options)
    : object_factory_parameterst(options)
  {
  }
};

/// Parse the java object factory parameters from a given command line
/// \param cmdline Command line
/// \param [out] options The options object that will be updated
void parse_java_object_factory_options(
  const cmdlinet &cmdline,
  optionst &options);

#endif
