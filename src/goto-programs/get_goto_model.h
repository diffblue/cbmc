/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H

class cmdlinet;
class message_handlert;
class goto_modelt;

goto_modelt get_goto_model(
  const cmdlinet &,
  message_handlert &);

#endif
