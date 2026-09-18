extern "C" void __CPROVER_assert(bool, const char *);
// GCC and Clang do not pack a member of non-POD class type ("ignoring packed
// attribute because of unpacked non-POD field"); a member-level packed
// attribute is honoured.  (GCC extension; POD as in C++03 [class]/9.)
struct EB {};
struct NP1 : EB { int i; };                 // non-POD (base)
struct NP2 { int i; NP2() : i(0) {} };      // non-POD (ctor)
struct NP3 { private: int i; };             // non-POD (private member)
struct POD { int i; };
struct A1 { char c; NP1 m; } __attribute__((packed));
struct A2 { char c; NP2 m; } __attribute__((packed));
struct A3 { char c; NP3 m; } __attribute__((packed));
struct A4 { char c; POD m; } __attribute__((packed));
struct A5 { char c; NP1 m __attribute__((packed)); };
struct NP5 : EB { long l; } __attribute__((packed));                 // a PACKED non-POD type
struct NP6 : EB { long l; } __attribute__((packed, aligned(8)));
struct A6 { char c; NP5 m; } __attribute__((packed));
struct A7 { char c; NP6 m; } __attribute__((packed));
int main()
{
  __CPROVER_assert(sizeof(A1) == 8 && alignof(A1) == 4 && __builtin_offsetof(A1, m) == 4, "A1 non-POD (base) member not packed");
  __CPROVER_assert(sizeof(A2) == 8 && alignof(A2) == 4 && __builtin_offsetof(A2, m) == 4, "A2 non-POD (constructor)");
  __CPROVER_assert(sizeof(A3) == 8 && alignof(A3) == 4 && __builtin_offsetof(A3, m) == 4, "A3 non-POD (private member)");
  __CPROVER_assert(sizeof(A4) == 5 && alignof(A4) == 1 && __builtin_offsetof(A4, m) == 1, "A4 POD member packed");
  __CPROVER_assert(sizeof(A5) == 5 && alignof(A5) == 1 && __builtin_offsetof(A5, m) == 1, "A5 member-level packed attribute honoured");
  __CPROVER_assert(sizeof(A6) == 9 && alignof(A6) == 1 && __builtin_offsetof(A6, m) == 1, "A6 a packed non-POD member type is packed (GCC: \"unpacked\" non-POD field)");
  __CPROVER_assert(sizeof(A7) == 9 && alignof(A7) == 1 && __builtin_offsetof(A7, m) == 1, "A7 packed+aligned(8) non-POD member type is packed too");
  return 0;
}
