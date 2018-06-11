#include <cassert>

#define FUNCTION

template<int m>
class myarray {

  int elt[m];

public:
  int& operator[] (int idx) {
    return elt[idx];
  }
};

#ifdef FUNCTION
void check(myarray<4> &y)
{
  assert(y[0] == 0);
  assert(y[3] == 3);
}
#endif

int main(void) {
  myarray<4> x;

  for (int i=0; i<4; i++) {
    x[i] = i;
  }

  assert(x[0] == 0);
  assert(x[3] == 3);

#ifdef FUNCTION
  check(x); //this doesn't work
#else
  myarray<4> &y = x; //this works
  assert(y[0] == 0);
  assert(y[3] == 3);
#endif

  return 0;
}
