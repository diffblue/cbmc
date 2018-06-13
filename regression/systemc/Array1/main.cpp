#include <cassert>

#define COPY

typedef unsigned uint;

template <class T, uint m>
class myarray {

  T elt[m];

public:
#if 0
  myarray &operator=(const myarray &other) {
    for (int i=0; i<m; i++) {
      elt[i] = other.elt[i];
    }
    return *this;
  }
#endif

  T& operator[] (int idx) {
    return elt[idx];
  }
};

#ifdef COPY
myarray<uint, 3> rev3u(myarray<uint, 3> x) {
  myarray<uint, 3> y;
  y[0] = x[2];
  y[1] = x[1];
  y[2] = x[0];
  return y;
}

#else

void rev3u(myarray<uint, 3> x, myarray<uint, 3> &y) {
  y[0] = x[2];
  y[1] = x[1];
  y[2] = x[0];
}
#endif

extern bool arbb();
extern uint arbu();

int main(void) {
  myarray<bool, 4> arrb;

  for (int i=0; i<4; i++) {
    bool cond = (i%2 == 0);
    arrb[i] = cond;
  }

  assert(arrb[0] == true);
  assert(arrb[1] == false);
  assert(arrb[2] == true);
  assert(arrb[3] == false);

  myarray<uint, 3> arru;
  for (int i=0; i<3; i++) {
    arru[i] = arbu();
  }

  myarray<uint, 3> arru2;
#ifdef COPY
  arru2 = rev3u(arru); //problem: copy constructor refuses to copy array (solved)
                       //new problem: byte_extract_little_endian ignored
#else
  rev3u(arru,arru2);
#endif
  assert (arru2[0] == arru[2]);
  assert (arru2[1] == arru[1]);
  assert (arru2[2] == arru[0]);

  return 0;
}
