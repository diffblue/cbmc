#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H

#include <cstddef>

struct abstract_object_statisticst
{
  std::size_t number_of_interval_abstract_objects = 0;
  std::size_t number_of_single_value_intervals = 0;
  std::size_t number_of_structs = 0;
  std::size_t number_of_arrays = 0;
  std::size_t number_of_pointers = 0;
  std::size_t number_of_constants = 0;
  std::size_t number_of_globals = 0;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H
