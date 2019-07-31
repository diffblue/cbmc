/// Author: Diffblue Ltd.

#ifndef CPROVER_JAVA_BYTECODE_GENERIC_PARAMETER_SPECIALIZATION_MAP_H
#define CPROVER_JAVA_BYTECODE_GENERIC_PARAMETER_SPECIALIZATION_MAP_H

#include <stack>
#include <vector>

#include <util/string_utils.h>

#include "expr2java.h"
#include "java_types.h"

/// A map from generic type parameters to their specializations (type arguments)
/// We need to map from the names of parameters to the container (class or
/// method) that contains them as well as the particular specialization of that
/// parameter. However we do not need the name of the container, merely the full
/// set of specializations for the parameters of that container.
/// We store a stack of specializations for each container for a particular
/// context. Finding the value for a type parameter is a matter of following
/// the specialization for that parameter, unwinding the stack of its container
/// as you do so and repeating until one reaches a non-generic type.
class generic_parameter_specialization_mapt
{
private:
  /// The index of the container and the type parameter inside that container
  struct container_paramt
  {
    std::size_t container_index;
    std::size_t param_index;
  };
  /// A map from parameter names to container_paramt instances
  std::unordered_map<irep_idt, container_paramt> param_to_container;
  /// The list of containers and, for each one, the stack of lists of
  /// specializations
  std::vector<std::stack<std::vector<reference_typet>>>
    container_to_specializations;

public:
  /// Insert a specialization for each type parameters of a container
  /// \param parameters: The type parameters
  /// \param types: The type arguments
  /// \returns: The index of the added container
  std::size_t insert(
    const std::vector<java_generic_parametert> &parameters,
    std::vector<reference_typet> types);

  /// Pop the top of the specialization stack for a given container
  /// \param container_index: The index of the container to pop
  void pop(std::size_t container_index);

  /// Pop the top of the specialization stack for the container associated with
  /// a given type parameter
  /// \param parameter_name: The name of the type parameter
  /// \returns: The specialization for the given type parameter, if there was
  ///   one before the pop, or an empty optionalt if the stack was empty
  optionalt<reference_typet> pop(const irep_idt &parameter_name);

  /// A wrapper for a generic_parameter_specialization_mapt and a namespacet
  /// that can be output to a stream
  struct printert
  {
    const generic_parameter_specialization_mapt &map;
    const namespacet &ns;

    printert(
      const generic_parameter_specialization_mapt &map,
      const namespacet &ns)
      : map(map), ns(ns)
    {
    }
  };

  template <typename ostreamt>
  friend ostreamt &operator<<(ostreamt &stm, const printert &map);
};

/// Output a generic_parameter_specialization_mapt wrapped in a
/// generic_parameter_specialization_mapt::printert to a stream
/// \tparam ostreamt: The type of stream to output to (not restricted to be
///   derived from std::ostream)
/// \param stm: The stream to output to
/// \param map: The generic_parameter_specialization_mapt printer to output
/// \returns: A reference to the stream passed in
template <typename ostreamt>
ostreamt &operator<<(
  ostreamt &stm,
  const generic_parameter_specialization_mapt::printert &map)
{
  if(map.map.container_to_specializations.empty())
    stm << "empty map";
  else
    stm << "map:\n";
  std::vector<std::vector<irep_idt>> container_to_params(
    map.map.container_to_specializations.size());
  for(const auto &elt : map.map.param_to_container)
  {
    std::vector<irep_idt> &params =
      container_to_params[elt.second.container_index];
    if(params.size() < elt.second.param_index + 1)
      params.resize(elt.second.param_index + 1);
    params[elt.second.param_index] = elt.first;
  }
  const namespacet &ns = map.ns;
  for(std::size_t index = 0; index < container_to_params.size(); ++index)
  {
    stm << "<";
    join_strings(
      stm,
      container_to_params.at(index).begin(),
      container_to_params.at(index).end(),
      ", ");
    stm << ">: ";
    std::stack<std::vector<reference_typet>> stack =
      map.map.container_to_specializations.at(index);
    while(!stack.empty())
    {
      stm << "<";
      join_strings(
        stm,
        stack.top().begin(),
        stack.top().end(),
        ", ",
        [&ns](const reference_typet &pointer_type) {
          if(is_java_generic_parameter(pointer_type))
          {
            return id2string(
              to_java_generic_parameter(pointer_type).get_name());
          }
          else
            return type2java(pointer_type, ns);
        });
      stm << ">, ";
      stack.pop();
    }
    stm << "\n";
  }
  return stm;
}

#endif // CPROVER_JAVA_BYTECODE_GENERIC_PARAMETER_SPECIALIZATION_MAP_H
