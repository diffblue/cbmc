/*******************************************************************\

 Module: Generic Arguments Name Builder

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// file - A class to aid in building the name of specialized generic classes.
/// Allows for custom builder function for a single argument name.

#include <sstream>
#include "generic_arguments_name_builder.h"
#include "java_utils.h"

std::string generic_arguments_name_buildert::finalize()
{
  std::ostringstream name_buffer;

  if(!type_arguments.empty())
  {
    bool first = true;
    for(const auto &argument : type_arguments)
    {
      if(first)
      {
        name_buffer << "<";
        first = false;
      }
      else
      {
        name_buffer << ", ";
      }

      name_buffer << argument_name_printer(argument);
    }
    name_buffer << ">";
    type_arguments.clear();
  }

  return name_buffer.str();
}
