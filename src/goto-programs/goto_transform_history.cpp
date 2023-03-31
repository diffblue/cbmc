// Author: Diffblue Ltd.

#include "goto_transform_history.h"

#include <util/invariant.h>

#include "goto_function.h"
#include "goto_functions.h"

void goto_transform_historyt::add(goto_transform_kindt transform)
{
  INVARIANT(
    is_valid_transform_kind(transform),
    "History should be built using valid transformations.");
  _transforms.push_back(transform);
}

const goto_transform_historyt::transformst &
goto_transform_historyt::transforms() const
{
  return _transforms;
}

bool is_valid_transform_kind(const goto_transform_kindt transform)
{
  switch(transform)
  {
  case goto_transform_kindt::link_to_library:
  case goto_transform_kindt::string_instrumentation:
  case goto_transform_kindt::remove_function_pointers:
  case goto_transform_kindt::mm_io:
  case goto_transform_kindt::instrument_preconditions:
  case goto_transform_kindt::goto_partial_inline:
  case goto_transform_kindt::remove_returns:
  case goto_transform_kindt::remove_vector:
  case goto_transform_kindt::remove_complex:
  case goto_transform_kindt::rewrite_union:
  case goto_transform_kindt::transform_assertions_assumptions:
  case goto_transform_kindt::adjust_float_expressions:
  case goto_transform_kindt::string_abstraction:
  case goto_transform_kindt::remove_unused_functions:
  case goto_transform_kindt::remove_skip:
  case goto_transform_kindt::label_properties:
    return true;
    // Note: There is deliberately no `default:` case here in order to ensure
    // that there is a compilation error if the enum is updated without
    // updating the validation.
  }
  return false;
}

void add_history_transform(
  goto_transform_kindt transform_kind,
  goto_functiont &function)
{
  function.history.add(transform_kind);
}

void add_history_transform(
  goto_transform_kindt transform_kind,
  goto_functionst &functions)
{
  for(auto &function_pair : functions.function_map)
  {
    add_history_transform(transform_kind, function_pair.second);
  }
}
