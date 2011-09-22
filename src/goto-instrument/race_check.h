/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_RACE_DETECTION_H
#define CPROVER_GOTO_PROGRAMS_RACE_DETECTION_H

#include <pointer-analysis/value_sets.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

void race_check(
  value_setst &value_sets,
  class contextt &context,
  goto_programt &goto_program);

void race_check(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions);

#endif
