#include <cassert>

class myarray {

  int elt[4];

public:
  int& operator[] (int idx) {
    return elt[idx];
  }
};

int main(void) {
  myarray x;

  for (int i=0; i<4; i++) {
    x[i] = i;
  }

  assert(x[0] == 0);
  assert(x[3] == 3);

  myarray y = x; //copy constructor does not typecheck
  assert(y[0] == 0);
  assert(y[3] == 3);

  return 0;
}
