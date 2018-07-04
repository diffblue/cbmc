#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H

#include <cstddef>

struct abstract_object_statisticst
{
  std::size_t number_of_interval_abstract_objects;
  std::size_t number_of_single_value_intervals;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_STATISTICS_H
