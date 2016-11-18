
#include "parameter_indices.h"

std::map<irep_idt,std::size_t> get_parameter_indices(const code_typet& fn_type)
{
  std::map<irep_idt,std::size_t>  parameter_indices;
  for (std::size_t  i = 0UL; i != fn_type.parameters().size(); ++i)
    parameter_indices.insert({fn_type.parameters().at(i).get_identifier(),i});
  return parameter_indices;
}
