/*******************************************************************\

Module: Dynamic frame condition checking for loop contracts

Author: Qinheping Hu, qinhh@amazon.com
Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Functions that allow to tag GOTO instructions with loop identifiers and
/// loop instruction type: head, body, exiting, latch.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LOOP_TAGS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LOOP_TAGS_H

#include <goto-programs/goto_program.h>

void dfcc_set_loop_id(
  goto_programt::instructiont::targett &target,
  std::size_t loop_id);

bool dfcc_has_loop_id(
  const goto_programt::instructiont::targett &target,
  std::size_t loop_id);

optionalt<std::size_t>
dfcc_get_loop_id(const goto_programt::instructiont::targett &target);

void dfcc_set_loop_head(goto_programt::instructiont::targett &target);
bool dfcc_is_loop_head(const goto_programt::instructiont::targett &target);

void dfcc_set_loop_body(goto_programt::instructiont::targett &target);
bool dfcc_is_loop_body(const goto_programt::instructiont::targett &target);

void dfcc_set_loop_exiting(goto_programt::instructiont::targett &target);
bool dfcc_is_loop_exiting(const goto_programt::instructiont::targett &target);

void dfcc_set_loop_latch(goto_programt::instructiont::targett &target);
bool dfcc_is_loop_latch(const goto_programt::instructiont::targett &target);

void dfcc_set_loop_top_level(goto_programt::instructiont::targett &target);
bool dfcc_is_loop_top_level(const goto_programt::instructiont::targett &target);

void dfcc_remove_loop_tags(source_locationt &source_location);
void dfcc_remove_loop_tags(goto_programt &goto_program);
void dfcc_remove_loop_tags(goto_programt::targett &target);
#endif
