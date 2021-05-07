/*******************************************************************\

Module:  Prepend/ splice a 0-ary function call in the beginning of a function 
e.g. for setting/ modelling the global environment

Author: Konstantinos Pouliasis

Date: July 2017

\*******************************************************************/

/// \file
/// Harnessing for goto functions

#ifndef CPROVER_GOTO_INSTRUMENT_SPLICE_CALL_H
#define CPROVER_GOTO_INSTRUMENT_SPLICE_CALL_H

#include <string>

class goto_functionst;
class message_handlert;
class symbol_tablet;

bool splice_call(
    goto_functionst &goto_functions,
    const std::string &callercallee,
    const symbol_tablet &symbol_table,
    message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_SPLICE_CALL_H
