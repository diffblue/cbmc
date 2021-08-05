/*******************************************************************\

  Module: A visitor class to update the last_written_locations of any visited
   abstract_object with a given set of locations.

 Author: Jez Higgins

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_LOCATION_UPDATE_VISITOR_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_LOCATION_UPDATE_VISITOR_H

#include "abstract_object.h"

class location_update_visitort
  : public abstract_objectt::abstract_object_visitort
{
public:
  explicit location_update_visitort(
    const abstract_objectt::locationst &locations)
    : locations(locations)
  {
  }

  abstract_object_pointert
  visit(const abstract_object_pointert &element) const override
  {
    return element->update_location_context(locations);
  }

private:
  const abstract_objectt::locationst &locations;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_LOCATION_UPDATE_VISITOR_H
