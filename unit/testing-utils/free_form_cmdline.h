/*******************************************************************\

 Module: Unit test utilities

 Author: Diffblue Limited.

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_FREE_FORM_CMDLINE_H
#define CPROVER_TESTING_UTILS_FREE_FORM_CMDLINE_H

#include <util/cmdline.h>

/// An implementation of cmdlinet to be used in tests. It does not require
/// specifying exactly what flags are supported and instead allows setting any
/// flag
class free_form_cmdlinet : public cmdlinet
{
public:
  void add_flag(std::string flag);
  void add_option(std::string flag, std::string value);

private:
  void create_flag(const std::string &flag_name);
};

#endif // CPROVER_TESTING_UTILS_FREE_FORM_CMDLINE_H
