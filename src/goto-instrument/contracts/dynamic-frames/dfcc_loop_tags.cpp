/*******************************************************************\

Module: Dynamic frame condition checking

Author: Qinheping Hu, qinhh@amazon.com
Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

#include "dfcc_loop_tags.h"

const irep_idt ID_loop_id = "loop-id";
const irep_idt ID_loop_head = "loop-head";
const irep_idt ID_loop_body = "loop-body";
const irep_idt ID_loop_latch = "loop-latch";
const irep_idt ID_loop_exiting = "loop-exiting";
const irep_idt ID_loop_top_level = "loop-top-level";

void dfcc_set_loop_id(
  goto_programt::instructiont::targett &target,
  const std::size_t loop_id)
{
  target->source_location_nonconst().set(ID_loop_id, loop_id);
}

optionalt<std::size_t>
dfcc_get_loop_id(const goto_programt::instructiont::targett &target)
{
  if(target->source_location_nonconst().get(ID_loop_id).empty())
    return {};

  return target->source_location_nonconst().get_size_t(ID_loop_id);
}

bool dfcc_has_loop_id(
  const goto_programt::instructiont::targett &target,
  std::size_t loop_id)
{
  auto loop_id_opt = dfcc_get_loop_id(target);
  return loop_id_opt.has_value() && loop_id_opt.value() == loop_id;
}

static void dfcc_set_loop_tag(
  goto_programt::instructiont::targett &target,
  const irep_idt &tag)
{
  target->source_location_nonconst().set(tag, true);
}

static bool has_loop_tag(
  const goto_programt::instructiont::targett &target,
  const irep_idt &tag)
{
  return target->source_location().get_bool(tag);
}

void dfcc_set_loop_head(goto_programt::instructiont::targett &target)
{
  dfcc_set_loop_tag(target, ID_loop_head);
}

bool dfcc_is_loop_head(const goto_programt::instructiont::targett &target)
{
  return has_loop_tag(target, ID_loop_head);
}

void dfcc_set_loop_body(goto_programt::instructiont::targett &target)
{
  dfcc_set_loop_tag(target, ID_loop_body);
}

bool dfcc_is_loop_body(const goto_programt::instructiont::targett &target)
{
  return has_loop_tag(target, ID_loop_body);
}

void dfcc_set_loop_exiting(goto_programt::instructiont::targett &target)
{
  dfcc_set_loop_tag(target, ID_loop_exiting);
}

bool dfcc_is_loop_exiting(const goto_programt::instructiont::targett &target)
{
  return has_loop_tag(target, ID_loop_exiting);
}

void dfcc_set_loop_latch(goto_programt::instructiont::targett &target)
{
  dfcc_set_loop_tag(target, ID_loop_latch);
}

bool dfcc_is_loop_latch(const goto_programt::instructiont::targett &target)
{
  return has_loop_tag(target, ID_loop_latch);
}

void dfcc_set_loop_top_level(goto_programt::instructiont::targett &target)
{
  dfcc_set_loop_tag(target, ID_loop_top_level);
}

bool dfcc_is_loop_top_level(const goto_programt::instructiont::targett &target)
{
  return has_loop_tag(target, ID_loop_top_level);
}

void dfcc_remove_loop_tags(source_locationt &source_location)
{
  source_location.remove(ID_loop_id);
  source_location.remove(ID_loop_head);
  source_location.remove(ID_loop_body);
  source_location.remove(ID_loop_exiting);
  source_location.remove(ID_loop_latch);
  source_location.remove(ID_loop_top_level);
}

void dfcc_remove_loop_tags(goto_programt::targett &target)
{
  dfcc_remove_loop_tags(target->source_location_nonconst());
}

void dfcc_remove_loop_tags(goto_programt &goto_program)
{
  for(auto target = goto_program.instructions.begin();
      target != goto_program.instructions.end();
      target++)
  {
    dfcc_remove_loop_tags(target);
  }
}
