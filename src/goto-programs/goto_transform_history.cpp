// Author: Diffblue Ltd.

#include "goto_transform_history.h"

void goto_transform_historyt::add(goto_transform_kindt transform)
{
  _transforms.push_back(transform);
}

const goto_transform_historyt::transformst &
goto_transform_historyt::transforms() const
{
  return _transforms;
}
