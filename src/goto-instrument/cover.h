/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

/// \file
/// Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_H
#define CPROVER_GOTO_INSTRUMENT_COVER_H

#include "cover_filter.h"
#include "cover_instrument.h"
#include "util/make_unique.h"

class message_handlert;
class cmdlinet;
class optionst;

enum class coverage_criteriont
{
  LOCATION,
  BRANCH,
  DECISION,
  CONDITION,
  PATH,
  MCDC,
  ASSERTION,
  COVER // __CPROVER_cover(x) annotations
};

struct cover_configt
{
  bool keep_assertions;
  bool traces_must_terminate;
  irep_idt mode;
  function_filterst function_filters;
  // cover instruments point to goal_filters, so they must be stored on the heap
  std::unique_ptr<goal_filterst> goal_filters =
    util_make_unique<goal_filterst>();
  cover_instrumenterst cover_instrumenters;
};

void instrument_cover_goals(
  const symbol_tablet &,
  const cover_configt &,
  goto_functionst &,
  coverage_criteriont,
  message_handlert &message_handler);

void instrument_cover_goals(
  const symbol_tablet &,
  const cover_configt &,
  goto_programt &,
  coverage_criteriont,
  message_handlert &message_handler);

cover_configt
get_cover_config(const optionst &, const symbol_tablet &, message_handlert &);

cover_configt get_cover_config(
  const optionst &,
  const irep_idt &main_function_id,
  const symbol_tablet &,
  message_handlert &);

void instrument_cover_goals(
  const cover_configt &,
  goto_model_functiont &,
  message_handlert &);

void parse_cover_options(const cmdlinet &, optionst &);

bool instrument_cover_goals(
  const cover_configt &,
  const symbol_tablet &,
  goto_functionst &,
  message_handlert &);

bool instrument_cover_goals(
  const cover_configt &,
  goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_COVER_H
