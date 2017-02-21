/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>

class struct_abstract_objectt:public abstract_objectt
{
public:
  explicit struct_abstract_objectt(const typet &type);
  struct_abstract_objectt(const typet &type, bool top, bool bottom);
  explicit struct_abstract_objectt(const struct_abstract_objectt &old);
  explicit struct_abstract_objectt(const constant_exprt &expr);

  CLONE
  MERGE(abstract_objectt)
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H
