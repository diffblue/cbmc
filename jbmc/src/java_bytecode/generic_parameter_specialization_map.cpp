/// Author: Diffblue Ltd.

#include "generic_parameter_specialization_map.h"

std::size_t generic_parameter_specialization_mapt::insert(
  const std::vector<java_generic_parametert> &parameters,
  std::vector<reference_typet> types)
{
  PRECONDITION(!parameters.empty());
  const auto first_param_it =
    param_to_container.find(parameters.front().get_name());
  std::size_t container_index;
  if(first_param_it == param_to_container.end())
  {
    container_index = container_to_specializations.size();
    container_to_specializations.emplace_back();
    std::size_t param_index = 0;
    for(const java_generic_parametert &parameter : parameters)
    {
      const auto result = param_to_container.emplace(
        parameter.get_name(), container_paramt{container_index, param_index++});
      INVARIANT(
        result.second, "Some type parameters are already mapped but not all");
    }
  }
  else
  {
    container_index = first_param_it->second.container_index;
    std::size_t param_index = 0;
    for(const java_generic_parametert &parameter : parameters)
    {
      const auto param_it = param_to_container.find(parameter.get_name());
      INVARIANT(
        param_it != param_to_container.end(),
        "Some type parameters are already mapped but not all");
      INVARIANT(
        param_it->second.container_index == container_index,
        "Not all type parameters are assigned to same container");
      INVARIANT(
        param_it->second.param_index == param_index,
        "Type parameters have been encountered in two different orders");
      ++param_index;
    }
  }
  container_to_specializations[container_index].push(std::move(types));
  return container_index;
}

void generic_parameter_specialization_mapt::pop(std::size_t container_index)
{
  container_to_specializations.at(container_index).pop();
}

optionalt<reference_typet>
generic_parameter_specialization_mapt::pop(const irep_idt &parameter_name)
{
  const auto types_it = param_to_container.find(parameter_name);
  if(types_it == param_to_container.end())
    return {};
  std::stack<std::vector<reference_typet>> &stack =
    container_to_specializations.at(types_it->second.container_index);
  if(stack.empty())
    return {};
  reference_typet result = stack.top().at(types_it->second.param_index);
  stack.pop();
  return result;
}
