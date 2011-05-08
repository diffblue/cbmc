/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

class recursion_countert
{
public:
  recursion_countert(unsigned &_cnt):cnt(_cnt)
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
