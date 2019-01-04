/*******************************************************************\

Module: Coverage Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Filters for the Coverage Instrumentation

#include "cover_filter.h"

#include <linking/static_lifetime_init.h>

/// Filter out functions that are not considered provided by the user
/// \param identifier: a function name
/// \param goto_function: a goto function
/// \return returns true if function is considered user-provided
bool internal_functions_filtert::operator()(
  const irep_idt &identifier,
  const goto_functionst::goto_functiont &goto_function) const
{
  if(identifier == goto_functionst::entry_point())
    return false;

  if(identifier == INITIALIZE_FUNCTION)
    return false;

  if(goto_function.is_hidden())
    return false;

  // ignore Java built-ins (synthetic functions)
  if(has_prefix(id2string(identifier), "java::array["))
    return false;

  // ignore if built-in library
  if(
    !goto_function.body.instructions.empty() &&
    goto_function.body.instructions.front().source_location.is_built_in())
    return false;

  return true;
}

/// Filter functions whose name match the regex
/// \param identifier: a function name
/// \param goto_function: a goto function
/// \return returns true if the function name matches
bool include_pattern_filtert::operator()(
  const irep_idt &identifier,
  const goto_functionst::goto_functiont &goto_function) const
{
  (void)goto_function; // unused parameter
  std::smatch string_matcher;
  return std::regex_match(id2string(identifier), string_matcher, regex_matcher);
}

/// Call a goto_program non-trivial if it has:
///  * Any declarations
///  * At least 2 branches
///  * At least 5 assignments
/// These criteria are arbitrarily chosen.
/// \param identifier: a function name
/// \param goto_function: a goto function
/// \return returns true if non-trivial
bool trivial_functions_filtert::operator()(
  const irep_idt &identifier,
  const goto_functionst::goto_functiont &goto_function) const
{
  (void)identifier; // unused parameter
  unsigned long count_assignments = 0, count_goto = 0;
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_goto())
    {
      if((++count_goto) >= 2)
        return true;
    }
    else if(i_it->is_assign())
    {
      if((++count_assignments) >= 5)
        return true;
    }
    else if(i_it->is_decl())
      return true;
  }

  return false;
}

/// Filter goals at source locations considered internal
/// \param source_location: source location of the current goal
/// \return true : if the given source location is not considered internal
bool internal_goals_filtert::
operator()(const source_locationt &source_location) const
{
  if(source_location.get_file().empty())
    return false;

  if(source_location.is_built_in())
    return false;

  return true;
}
