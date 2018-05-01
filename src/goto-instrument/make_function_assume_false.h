/*******************************************************************\

Module: Make function assume false

Author: Elizabeth Polgreen

Date: November 2017

\*******************************************************************/

/// \file
/// Make function assume false

#ifndef CPROVER_GOTO_INSTRUMENT_MAKE_FUNCTION_ASSUME_FALSE_H
#define CPROVER_GOTO_INSTRUMENT_MAKE_FUNCTION_ASSUME_FALSE_H

#include <list>
#include <string>

#include <util/irep.h>

class goto_modelt;
class message_handlert;

void make_functions_assume_false(
  goto_modelt &,
  const std::list<std::string> &names,
  message_handlert &);



#endif /* CPROVER_GOTO_INSTRUMENT_MAKE_FUNCTION_ASSUME_FALSE_H */
