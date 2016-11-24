#include <assert.h>

struct S
{
  int z;
  int a[]; // an incomplete array!
};

struct S s={ .z=1, .a={ 2, 3, 4 } };
struct S t={ 1, { 2, 3, 4 } };
struct S u={ z: 1, a: { 2, 3, 4 } };

int main()
{
  assert(s.z==1);
  assert(s.a[0]==2);
  assert(s.a[1]==3);
  assert(s.a[2]==4);

  assert(t.z==1);
  assert(t.a[0]==2);
  assert(t.a[1]==3);
  assert(t.a[2]==4);

  assert(u.z==1);
  assert(u.a[0]==2);
  assert(u.a[1]==3);
  assert(u.a[2]==4);
}
