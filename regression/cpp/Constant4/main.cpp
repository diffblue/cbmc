typedef unsigned UINT32;
typedef const UINT32 CONST_UINT32;

struct A {
  // these are proper constants in C++
  static const UINT32 size1 = 3;
  static CONST_UINT32 size2 = 3;

  char array1[size1];
  char array2[size2];
};

struct B {
  typedef unsigned B_UINT32;
  typedef const B_UINT32 B_CONST_UINT32;

  static const B_UINT32 size1 = 3;
  static B_CONST_UINT32 size2 = 3;

  char array1[size1];
  char array2[size2];
};

int main()
{
  A a;
  a.array1[0] = 'a';
  a.array1[1] = 'b';
  a.array1[2] = 'c';

  a.array2[0] = 'a';
  a.array2[1] = 'b';
  a.array2[2] = 'c';

  B b;
  b.array1[0] = 'a';
  b.array1[1] = 'b';
  b.array1[2] = 'c';

  b.array2[0] = 'a';
  b.array2[1] = 'b';
  b.array2[2] = 'c';
}
