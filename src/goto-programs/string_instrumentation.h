/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// String Abstraction

#ifndef CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
#define CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H

class exprt;
class goto_functionst;
class goto_modelt;
class symbol_table_baset;

void string_instrumentation(symbol_table_baset &, goto_functionst &);

void string_instrumentation(goto_modelt &);

exprt is_zero_string(const exprt &what, bool write = false);
exprt zero_string_length(const exprt &what, bool write=false);
exprt buffer_size(const exprt &what);

#endif // CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
