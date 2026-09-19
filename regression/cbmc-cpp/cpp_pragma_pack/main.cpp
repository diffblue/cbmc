extern "C" void __CPROVER_assert(bool, const char *);
// #pragma pack(n) (GCC/MSVC extension) in C++: caps the alignment of the
// members declared while it is in effect, as in the C front end.
enum class E2 : unsigned char { A = 0 };
#pragma pack(push, 1)
struct P1 { char c; int i; };
struct P2 { bool b : 1; long l; };
struct Q1 { unsigned m20; E2 m21 __attribute__((aligned(16))); };
struct Q4 { unsigned m20; E2 m21 __attribute__((aligned(16))); } __attribute__((packed));
struct Cls { char c; int i; int f() const { return i; } static int s; };
#pragma pack(pop)
#pragma pack(push, 2)
struct P3 { char c; long l; };
struct Q5 { unsigned m20; E2 m21 __attribute__((aligned(16))); };
#pragma pack(pop)
struct N { char c; int i; };
struct B0 { long l; short s; };            // 16, align 8
#pragma pack(push, 2)
struct D0 : B0 { char c; int i; };        // base kept as is, c at 16, i at 18, align capped to 2
#pragma pack(pop)
#pragma pack(4)
struct P4 { char c; double d; };
struct AN
{
  struct { long long a4; long a5; } __attribute__((aligned(16)));
  float m6;
  struct { int a11; int a12; } __attribute__((packed));
  unsigned short m13;
};
struct AM { char c; struct { long long a4; } __attribute__((aligned(16))) n; };
struct AU { char c; union { long a; } __attribute__((aligned(16))) u; char d; };
struct AB { char c; bool m __attribute__((aligned(8))); char d; } __attribute__((packed, aligned(4))); // the cap survives the bool's conversion
struct B1 { long l; short s; };
struct BD : B1 { char c; int i; };  // base subobject and the class capped at 4
#pragma pack()
struct N2 { char c; double d; };
#pragma pack(push, 2)
struct PA { char c; signed char m[8] __attribute__((packed, aligned(4))); }; // the cap also binds an ARRAY member's exact alignment
#pragma pack(pop)
int main()
{
  __CPROVER_assert(sizeof(P1) == 5 && alignof(P1) == 1, "pack(1)");
  __CPROVER_assert(sizeof(P2) == 9, "pack(1): bit-field + long");
  __CPROVER_assert(__builtin_offsetof(Q1, m21) == 4 && sizeof(Q1) == 5, "pack(1) caps an aligned(16) enum member");
  __CPROVER_assert(__builtin_offsetof(Q4, m21) == 4 && sizeof(Q4) == 5, "pack(1) + packed");
  __CPROVER_assert(sizeof(Cls) == 5, "member functions and static members are not laid out");
  __CPROVER_assert(sizeof(P3) == 10 && alignof(P3) == 2, "pack(2)");
  __CPROVER_assert(__builtin_offsetof(Q5, m21) == 4 && sizeof(Q5) == 6, "pack(2) caps aligned(16) to 2");
  __CPROVER_assert(sizeof(N) == 8, "after pop");
  __CPROVER_assert(sizeof(P4) == 12 && alignof(P4) == 4, "pack(4)");
  __CPROVER_assert(sizeof(N2) == 16, "after pack()");
  __CPROVER_assert(sizeof(AN) == 32 && alignof(AN) == 4 && __builtin_offsetof(AN, m6) == 16 && __builtin_offsetof(AN, a11) == 20 && __builtin_offsetof(AN, m13) == 28, "anonymous struct members under pack(4): the type's aligned(16) is capped");
  __CPROVER_assert(sizeof(AM) == 20 && alignof(AM) == 4 && __builtin_offsetof(AM, n) == 4, "named member of an aligned(16) anonymous type under pack(4)");
  __CPROVER_assert(sizeof(AU) == 24 && __builtin_offsetof(AU, u) == 4 && __builtin_offsetof(AU, d) == 20, "aligned(16) union type under pack(4): placed at 4, but 16 bytes long");
  __CPROVER_assert(sizeof(BD) == 20 && alignof(BD) == 4 && __builtin_offsetof(BD, i) == 16, "derived class under pack(4): base (12 bytes, align 4) then c, i");
  __CPROVER_assert(sizeof(D0) == 22 && alignof(D0) == 2 && __builtin_offsetof(D0, i) == 18, "derived class under pack(2) of a base defined outside: the base members do not raise the alignment above 2");
  __CPROVER_assert(sizeof(AB) == 8 && __builtin_offsetof(AB, m) == 4, "bool member with aligned(8) under pack(4): capped to 4");
  __CPROVER_assert(sizeof(PA) == 10 && __builtin_offsetof(PA, m) == 2, "packed, aligned(4) array member under pack(2): at 2");
  Cls k{1, 2};
  __CPROVER_assert(k.f() == 2, "member function of a packed class");
  return 0;
}
