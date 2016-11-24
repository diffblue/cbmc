#include <cassert>

enum IMPH_STATE
{
  IMPH_IDLE = 0,
  IMPH_ENABLED,
  IMPH_BGF_STOPPED
};

IMPH_STATE operator & (IMPH_STATE a, IMPH_STATE b)
{
  return IMPH_BGF_STOPPED;
}

int main()
{
  // constructor
  assert(IMPH_STATE()==IMPH_IDLE);

  // conversion from int
  assert(IMPH_STATE(2)==IMPH_BGF_STOPPED);
  
  // comparison with int
  assert(IMPH_BGF_STOPPED==2);
  
  // implicit conversion to int
  int z= IMPH_ENABLED | IMPH_BGF_STOPPED;
  
  // operator overloading
  IMPH_STATE x = IMPH_ENABLED & IMPH_BGF_STOPPED;
  assert(x==IMPH_BGF_STOPPED);
};
