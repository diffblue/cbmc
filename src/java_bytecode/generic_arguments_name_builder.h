/*******************************************************************\

 Module: Generic Arguments Name Builder

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// file - A class to aid in building the name of specialized generic classes.
/// Allows for custom builder function for a single argument name.

#ifndef CPROVER_JAVA_BYTECODE_GENERIC_ARGUMENTS_NAME_BUILDER_H
#define CPROVER_JAVA_BYTECODE_GENERIC_ARGUMENTS_NAME_BUILDER_H

#include "java_types.h"
#include <functional>

class generic_arguments_name_buildert
{
public:
  typedef std::function<std::string(const reference_typet &)>
    name_printert;

  explicit generic_arguments_name_buildert(
    const name_printert &argument_name_printer)
    : argument_name_printer(argument_name_printer)
  {
  }

  void add_argument(const reference_typet &argument)
  {
    PRECONDITION(!is_java_generic_parameter(argument));
    type_arguments.push_back(argument);
  }

  std::string finalize();

private:
  std::vector<reference_typet> type_arguments;
  name_printert argument_name_printer;
};

#endif // CPROVER_JAVA_BYTECODE_GENERIC_ARGUMENTS_NAME_BUILDER_H
