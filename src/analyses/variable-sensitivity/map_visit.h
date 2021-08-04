/*******************************************************************\

 Module: apply a function to values in a shared_map

 Author: Jez Higgins

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_MAP_VISIT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_MAP_VISIT_H

template <class mapt, class visitort>
bool visit_map(mapt &map, const visitort &visitor)
{
  bool modified = false;
  for(auto &item : map.get_view())
  {
    auto newval = visitor.visit(item.second);
    if(newval != item.second)
    {
      map.replace(item.first, std::move(newval));
      modified = true;
    }
  }
  return modified;
}

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_MAP_VISIT_H
