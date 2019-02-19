/*******************************************************************\

Module: Remove gcc's 'variable-length array members'

Author: Daniel Kroening

Date:   February 2019

\*******************************************************************/

/// \file
/// Remove gcc's 'variable-length array members'

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_VARIABLE_LENGTH_ARRAY_MEMBER_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_VARIABLE_LENGTH_ARRAY_MEMBER_H

class goto_functionst;
class goto_modelt;
class symbol_tablet;

void remove_variable_length_array_member(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_VARIABLE_LENGTH_ARRAY_MEMBER_H
