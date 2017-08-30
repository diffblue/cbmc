/*******************************************************************\

Module: Parameter indexing

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Parameter indexing

#include "parameter_indices.h"

/// Make a map useful for mapping from symbol expressions to actual or formal
/// parameter indices.
/// \par parameters: Code type
/// \return Map from parameter name to position
std::map<irep_idt, std::size_t> get_parameter_indices(const code_typet &fn_type)
{
  std::map<irep_idt, std::size_t>  parameter_indices;
  for(std::size_t i=0; i!=fn_type.parameters().size(); ++i)
    parameter_indices.insert({fn_type.parameters().at(i).get_identifier(), i});
  return parameter_indices;
}
