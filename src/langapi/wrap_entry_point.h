/*******************************************************************\

Module: Wrap the designated entry point into a while(true) loop.

Author: Diffblue Limited (c) 2017

Date: August 2017

\*******************************************************************/

#ifndef WRAP_ENTRY_POINT_H
#define WRAP_ENTRY_POINT_H

#include <util/std_code.h>

/// Command line option (to be shared by the different tools)
#define WRAP_ENTRY_POINT_IN_WHILE_TRUE "(wrap-entry-point-in-while)"

code_whilet wrap_entry_point_in_while(
  code_function_callt &call_main);

#endif // WRAP_ENTRY_POINT_H
