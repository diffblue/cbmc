/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_POINTER_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_POINTER_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>

class typet;
class constant_exprt;

class pointer_abstract_objectt:public abstract_objectt
{
public:
  explicit pointer_abstract_objectt(const typet &type);
  pointer_abstract_objectt(const typet &type, bool top, bool bottom);
  explicit pointer_abstract_objectt(const pointer_abstract_objectt &old);
  explicit pointer_abstract_objectt(const constant_exprt &expr);

  CLONE
  MERGE(abstract_objectt)
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_POINTER_ABSTRACT_OBJECT_H
