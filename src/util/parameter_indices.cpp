/*******************************************************************\

Module: Parameter indexing

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "parameter_indices.h"

/*******************************************************************\

Function: get_parameter_indices

  Inputs: Code type

 Outputs: Map from parameter name to position

 Purpose: Make a map useful for mapping from symbol expressions to
          actual or formal parameter indices.

\*******************************************************************/

std::map<irep_idt, std::size_t> get_parameter_indices(const code_typet &fn_type)
{
  std::map<irep_idt, std::size_t>  parameter_indices;
  for(std::size_t i=0; i!=fn_type.parameters().size(); ++i)
    parameter_indices.insert({fn_type.parameters().at(i).get_identifier(), i});
  return parameter_indices;
}
