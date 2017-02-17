/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_RECURSION_COUNTER_H
#define CPROVER_CPP_RECURSION_COUNTER_H

class recursion_countert
{
public:
  explicit recursion_countert(unsigned &_cnt):cnt(_cnt)
  {
    cnt++;
  }

  ~recursion_countert()
  {
    cnt--;
  }

protected:
  unsigned &cnt;
};

#endif // CPROVER_CPP_RECURSION_COUNTER_H
