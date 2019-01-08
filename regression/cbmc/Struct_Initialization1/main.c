#include <assert.h>

struct tag1 {
  int f;
  int : 32; // unnamed bit-field, ignored during initialization
  int g;
  int *p;
  int a[2];
} x;

struct tag1 y={ 1, 2, &x.f };

struct tag1 z={ 1>>3 };

struct tag1 array[]={ 1, 2, 0, 3, 4, 5, 6 };

struct tag1 S1={ .g=2, .p=0 };

struct tag2 {
  int a, b;
};

struct tag3 {
  struct tag2 s1, s2;
};

struct tag3 S2={ 1, 2, 3, 4 };

struct tag3 S3={ .s1={ 1, 2 }, .s2={ 3, 4 } };

int main() {
  assert(x.f == 0);
  assert(x.g == 0);
  assert(x.p == 0);

  assert(y.f==1);
  assert(y.g==2);
  assert(y.p==&x.f);

  assert(array[0].f==1);
  assert(array[1].g==6);

  assert(S1.f==0);
  assert(S1.g==2);
  assert(S1.p==0);

  assert(S2.s1.a==1);
  assert(S2.s1.b==2);
  assert(S2.s2.a==3);
  assert(S2.s2.b==4);

  assert(S3.s1.a==1);
  assert(S3.s1.b==2);
  assert(S3.s2.a==3);
  assert(S3.s2.b==4);
}
