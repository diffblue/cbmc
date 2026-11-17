/*******************************************************************\

Module: Check C++26 postcondition assertions

Author: Kiro

\*******************************************************************/

/// \file
/// Check the postcondition assertions of C++26 functions on normal exit
/// (N5008 [dcl.contract.func], [basic.contract.eval]).

#ifndef CPROVER_GOTO_PROGRAMS_INSTRUMENT_CPP_POSTCONDITIONS_H
#define CPROVER_GOTO_PROGRAMS_INSTRUMENT_CPP_POSTCONDITIONS_H

class goto_modelt;

/// For each function whose contract symbol (`contract::F`) the C++ front
/// end marked for checking, add the checks of its postcondition assertions
/// where the function exits normally.  Runs after
/// elide_cpp_returned_temporaries (a returned class object is then the
/// caller's result object) and remove_cpp_exceptions.
void instrument_cpp_postconditions(goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_INSTRUMENT_CPP_POSTCONDITIONS_H
