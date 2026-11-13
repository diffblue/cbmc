#include <assert.h>

// __auto_type v = init; is typeof(init) v = init;, but init is only evaluated
// (and its declarations only made) once. Each of these used to fail with a
// redeclaration of a symbol declared in a statement expression.
int main(void)
{
  int a = 3;

  // a single level of statement expression
  __auto_type v1 = ({
    int p = a;
    p + 1;
  });
  assert(v1 == 4);

  // typedefs, tags and enumeration constants
  __auto_type v2 = ({
    typedef long T;
    T p = a;
    p;
  });
  assert(sizeof(v2) == sizeof(long) && v2 == 3);
  __auto_type v3 = ({
    struct S
    {
      int x;
    } s = {a};
    s.x;
  });
  assert(v3 == 3);
  __auto_type v4 = ({
    enum E
    {
      K = 5
    };
    a + K;
  });
  assert(v4 == 8);
  __auto_type v5 = ({
    union U
    {
      int i;
      char c;
    } u;
    u.i = a;
    u;
  });
  assert(v5.i == 3);

  // local labels
  __auto_type v6 = ({
    __label__ out;
    int p = a;
    if(p)
      goto out;
    p = 0;
  out:
    p;
  });
  assert(v6 == 3);

  // statement expressions in sizeof and _Alignof
  __auto_type v7 = sizeof(({
    int p = a;
    p;
  }));
  assert(v7 == sizeof(int));
  __auto_type v8 = ({
    int k = _Alignof(({
      int p = a;
      p;
    }));
    k;
  });
  assert(v8 == _Alignof(int));

  // qualified __auto_type
  const __auto_type v9 = ({
    const __auto_type p = a;
    p + 1;
  });
  assert(v9 == 4);

  // in a for loop
  int s = 0;
  for(__auto_type i = ({
        int z = 0;
        z;
      });
      i < a;
      i++)
    s += i;
  assert(s == 3);

  return 0;
}
