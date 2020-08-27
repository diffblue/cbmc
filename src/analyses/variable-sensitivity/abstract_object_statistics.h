/*******************************************************************\

Module: Variable Sensitivity Domain

Author: Hannes Steffenhagen

\*******************************************************************/

/// \file
/// Statistics gathering for the variable senstivity domain

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H

#include <cstddef>

#include <util/memory_units.h>
struct abstract_object_statisticst
{
  std::size_t number_of_interval_abstract_objects = 0;
  std::size_t number_of_single_value_intervals = 0;
  std::size_t number_of_structs = 0;
  std::size_t number_of_arrays = 0;
  std::size_t number_of_pointers = 0;
  std::size_t number_of_constants = 0;
  std::size_t number_of_globals = 0;
  /// An underestimation of the memory usage of the abstract objects
  memory_sizet objects_memory_usage;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H
