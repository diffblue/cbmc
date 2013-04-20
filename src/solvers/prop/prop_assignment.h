/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_ASSIGNMENT_H
#define CPROVER_PROP_ASSIGNMENT_H

#include "literal.h"

class tvt;
class propt;

/*! \brief TO_BE_DOCUMENTED
*/
class prop_assignmentt
{
public:
  virtual ~prop_assignmentt();

  // satisfying assignment
  virtual tvt l_get(literalt a) const=0;
  virtual void set_assignment(literalt a, bool value)=0;
  virtual void copy_assignment_from(const propt &prop)=0;
};

#endif
