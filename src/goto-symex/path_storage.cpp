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

path_storaget::patht &path_fifot::peek()
{
  return paths.front();
}

void path_fifot::push(const path_storaget::patht &bp)
{
  paths.push_back(bp);
}

void path_fifot::pop()
{
  paths.pop_front();
}

std::size_t path_fifot::size() const
{
  return paths.size();
}
