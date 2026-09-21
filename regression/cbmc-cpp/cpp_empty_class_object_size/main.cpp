extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [class]/4, [intro.object]/9: a complete object of class type has a
// nonzero size -- an empty class is one byte (its alignment when over-aligned);
// an empty MEMBER occupies its byte, an empty BASE subobject may have zero size
// (the Itanium ABI empty base optimisation).  The class used to be a zero-sized
// object whose sizeof was special-cased to 1.
struct E
{
};
struct E2
{
  signed char : 0;
};
struct E3
{
  signed char : 0;
} __attribute__((aligned(2)));
struct E4
{
  int : 0;
};
struct E5
{
  char c;
  int : 0;
};
struct D : E
{
  char c;
};
struct EA
{
  E e;
  char c;
};
struct E6
{
  using vt = int;
  static int s;
  int f() const
  {
    return 1;
  }
};
struct M2
{
  E e1;
  E e2;
  char c;
};
struct D2 : E
{
  E2 e;
  char c;
};
struct alignas(8) E8
{
};
struct M8
{
  char c;
  E8 e;
  char d;
};
union EU
{
  void f() const
  {
  }
  int : 0;
} __attribute__((aligned(16))); // an empty union is an object too
struct alignas(16) A16
{
  char c;
};
struct alignas(16) E16
{
};
#pragma pack(push, 2)
struct PD1 : A16
{
  char d;
}; // a non-empty over-aligned base is capped by the pragma
struct PD2 : E16
{
  char d;
}; // an EMPTY over-aligned base is not (g++, clang)
struct PD6
{
  char x;
  E16 e;
  char d;
};
#pragma pack(pop)
int main()
{
  __CPROVER_assert(sizeof(E) == 1, "empty class has size 1");
  __CPROVER_assert(
    sizeof(E2) == 1, "unnamed zero-width bit-field only: size 1");
  __CPROVER_assert(sizeof(E3) == 2 && alignof(E3) == 2, "with aligned(2)");
  __CPROVER_assert(
    sizeof(E4) == 1 && alignof(E4) == 1, "int : 0 only: size 1, align 1");
  __CPROVER_assert(
    sizeof(E5) == 4 && alignof(E5) == 1, "char then int : 0: size 4");
  __CPROVER_assert(sizeof(D) == 1, "empty base optimisation");
  __CPROVER_assert(sizeof(EA) == 2, "empty member takes a byte");
  __CPROVER_assert(sizeof(E6) == 1, "only non-storage members: size 1");
  __CPROVER_assert(
    sizeof(M2) == 3 && __builtin_offsetof(M2, e2) == 1 &&
      __builtin_offsetof(M2, c) == 2,
    "two empty members take a byte each");
  __CPROVER_assert(
    sizeof(D2) == 2 && __builtin_offsetof(D2, e) == 0 &&
      __builtin_offsetof(D2, c) == 1,
    "an empty base takes no space, an empty member does");
  __CPROVER_assert(
    sizeof(E8) == 8 && alignof(E8) == 8 && sizeof(M8) == 24 &&
      __builtin_offsetof(M8, d) == 16,
    "over-aligned empty class");
  __CPROVER_assert(
    sizeof(EU) == 16 && alignof(EU) == 16,
    "empty union: one byte, padded to its alignment");
  __CPROVER_assert(
    sizeof(PD1) == 18 && alignof(PD1) == 2 && __builtin_offsetof(PD1, d) == 16,
    "alignas(16) base capped by pack(2)");
  __CPROVER_assert(
    sizeof(PD2) == 16 && alignof(PD2) == 16 && __builtin_offsetof(PD2, d) == 0,
    "empty alignas(16) base aligns the derived class even under pack(2)");
  __CPROVER_assert(
    sizeof(PD6) == 20 && __builtin_offsetof(PD6, d) == 18,
    "empty alignas(16) member: placement capped, 16 bytes long");
  E arr[3];
  E *p = &arr[1];
  __CPROVER_assert(
    p - arr == 1 && sizeof(arr) == 3, "array of empty objects: one byte each");
  E a, b;
  __CPROVER_assert(&a != &b, "distinct empty objects have distinct addresses");
  return 0;
}
