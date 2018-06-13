#include <cassert>

#define CLASS

#ifdef CLASS
class myarray {

  typedef bool base;
  base elt[4];

public:
  base &operator[] (int idx) {
    return elt[idx];
  }
};

#else

bool &get(bool *arr, int i)
{
  return arr[i];
}
#endif

int main(void) {

#ifndef CLASS
  bool arrb[4];

  for (int i=0; i<4; i++) {
    bool cond = (i%2 == 0);
    arrb[i] = cond;
  }

  assert(get(arrb,0) == true);

#else

  myarray arrb;

  for (int i=0; i<4; i++) {
    bool cond = (i%2 == 0);
    arrb[i] = cond;
  }

  assert(arrb[2] == true);
#endif
  return 0;
}
