/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

std::unique_ptr<path_storaget>
path_storaget::make(path_storaget::disciplinet discipline)
{
  switch(discipline)
  {
  case path_storaget::disciplinet::FIFO:
    return std::unique_ptr<path_fifot>(new path_fifot());
  }
  UNREACHABLE;
}

path_storaget::patht &path_fifot::private_peek()
{
  return paths.front();
}

void path_fifot::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

void path_fifot::private_pop()
{
  paths.pop_front();
}

std::size_t path_fifot::size() const
{
  return paths.size();
}
