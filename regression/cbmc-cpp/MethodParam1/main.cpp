#include <assert.h>
unsigned x;

class ct {
public:
  void f(int i) {
    x=x+i;
  }
};

int main() {
  unsigned r;
  x=r%3;
  ct c;
  c.f(2);
  assert(x<4);
  assert(x<5);
}

