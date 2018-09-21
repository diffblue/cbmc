/*******************************************************************\

 Module: Unit test utilities

 Author: Diffblue Limited.

\*******************************************************************/

#include "free_form_cmdline.h"

/// Create a command line option that can be set
/// \param flag_name: The name of the command line option to support
void free_form_cmdlinet::create_flag(const std::string &flag_name)
{
  optiont option;
  option.optstring = flag_name;
  options.push_back(option);
}

/// Equivalent to specifying --flag for the command line
/// \param flag: The name of the flag to specify
void free_form_cmdlinet::add_flag(std::string flag)
{
  create_flag(flag);
  set(flag);
}

/// Equivalent to specifying --flag value
/// \param flag: The name of the flag to specify
/// \param value: The value to the set the command line option to
void free_form_cmdlinet::add_option(std::string flag, std::string value)
{
  create_flag(flag);
  set(flag, value);
}
