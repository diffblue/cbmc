extern "C" void __CPROVER_assert(bool, const char *);
// GCC and Clang do not pack a member of non-POD class type ("ignoring packed
// attribute because of unpacked non-POD field"); a member-level packed
// attribute is honoured.  (GCC extension; POD as in C++03 [class]/9.)
struct EB
{
};
struct NP1 : EB
{
  int i;
}; // non-POD (base)
struct NP2
{
  int i;
  NP2() : i(0)
  {
  }
}; // non-POD (ctor)
struct NP3
{
private:
  int i;
}; // non-POD (private member)
struct POD
{
  int i;
};
struct A1
{
  char c;
  NP1 m;
} __attribute__((packed));
struct A2
{
  char c;
  NP2 m;
} __attribute__((packed));
struct A3
{
  char c;
  NP3 m;
} __attribute__((packed));
struct A4
{
  char c;
  POD m;
} __attribute__((packed));
struct A5
{
  char c;
  NP1 m __attribute__((packed));
};
struct NP5 : EB
{
  long l;
} __attribute__((packed)); // a PACKED non-POD type
struct NP6 : EB
{
  long l;
} __attribute__((packed, aligned(8)));
struct A6
{
  char c;
  NP5 m;
} __attribute__((packed));
struct A7
{
  char c;
  NP6 m;
} __attribute__((packed));
struct alignas(16) S3
{
  int i;
  S3() : i(0)
  {
  }
}; // non-POD, alignment 16
struct A8
{
  char c;
  S3 m __attribute__((aligned(4)));
} __attribute__((packed)); // aligned(4) cannot lower 16
struct NPX
{
  long l;
  NPX()
  {
  }
};
struct B16
{
  int m __attribute__((aligned(16)));
};
// GCC (check_field_decls): a packed class with a data member of UNPACKED non-POD
// class type -- whatever the member's own attributes -- is not a packed type
// itself: its other members are still packed, but as a member of another
// packed struct it is aligned naturally.  Bases do not count.
struct Y1
{
  NPX m __attribute__((packed, aligned(4)));
} __attribute__((packed));
struct Y2 : NPX
{
  NPX m __attribute__((packed));
} __attribute__((packed));
struct Y4 : B16
{
  NPX m __attribute__((packed));
} __attribute__((packed));
struct Y5 : NPX, B16
{
  int m;
} __attribute__((packed));
struct X6
{
  NPX m;
  char c;
  int a;
} __attribute__((packed));
struct C1
{
  char c;
  Y1 m;
} __attribute__((packed));
struct C2
{
  char c;
  Y2 m;
} __attribute__((packed));
struct C4
{
  char c;
  Y4 m;
} __attribute__((packed));
struct C5
{
  char c;
  Y5 m;
} __attribute__((packed));
struct NPU
{
  long l;
  NPU()
  {
  }
};
union alignas(16) UN
{
  double d;
  NPU n;
}; // a union with a non-POD member is a non-POD
struct PU
{
  short m : 2;
  int m2 : 21;
  UN u;
} __attribute__((packed, aligned(2)));
struct EB5
{
};
#pragma pack(push, 1)
struct PP : public EB5
{
  signed char m7;
  unsigned char m8[8];
}; // non-POD, defined under pack(1): NOT a packed type
#pragma pack(pop)
typedef PP __attribute__((aligned(4))) PPT;
struct PQ
{
  unsigned long : 0;
  PPT m20;
  PQ()
  {
  }
} __attribute__((packed));
int main()
{
  __CPROVER_assert(
    sizeof(A1) == 8 && alignof(A1) == 4 && __builtin_offsetof(A1, m) == 4,
    "A1 non-POD (base) member not packed");
  __CPROVER_assert(
    sizeof(A2) == 8 && alignof(A2) == 4 && __builtin_offsetof(A2, m) == 4,
    "A2 non-POD (constructor)");
  __CPROVER_assert(
    sizeof(A3) == 8 && alignof(A3) == 4 && __builtin_offsetof(A3, m) == 4,
    "A3 non-POD (private member)");
  __CPROVER_assert(
    sizeof(A4) == 5 && alignof(A4) == 1 && __builtin_offsetof(A4, m) == 1,
    "A4 POD member packed");
  __CPROVER_assert(
    sizeof(A5) == 5 && alignof(A5) == 1 && __builtin_offsetof(A5, m) == 1,
    "A5 member-level packed attribute honoured");
  __CPROVER_assert(
    sizeof(A6) == 9 && alignof(A6) == 1 && __builtin_offsetof(A6, m) == 1,
    "A6 a packed non-POD member type is packed (GCC: \"unpacked\" non-POD "
    "field)");
  __CPROVER_assert(
    sizeof(A7) == 9 && alignof(A7) == 1 && __builtin_offsetof(A7, m) == 1,
    "A7 packed+aligned(8) non-POD member type is packed too");
  __CPROVER_assert(
    __builtin_offsetof(A8, m) == 16 && alignof(A8) == 16,
    "A8 member aligned(4) on a non-POD member: natural 16 stays");
  __CPROVER_assert(
    sizeof(X6) == 16 && alignof(X6) == 8 && __builtin_offsetof(X6, a) == 9,
    "X6 other members still packed, class alignment natural");
#ifndef __clang__ // clang packs these (the extension differs between the compilers)
  __CPROVER_assert(
    __builtin_offsetof(C1, m) == 4,
    "Y1: packed cancelled by an unpacked non-POD member, alignment 4");
  __CPROVER_assert(
    __builtin_offsetof(C2, m) == 8, "Y2: alignment 8 from the base");
  __CPROVER_assert(
    __builtin_offsetof(C4, m) == 16, "Y4: alignment 16 from the base");
#endif
  __CPROVER_assert(
    __builtin_offsetof(C5, m) == 1, "Y5: non-POD bases only, stays packed");
  __CPROVER_assert(
    __builtin_offsetof(PU, u) == 16 && alignof(PU) == 16 && sizeof(PU) == 32,
    "non-POD union member of a packed struct is not packed");
  __CPROVER_assert(
    alignof(PP) == 1 && alignof(PPT) == 4 && alignof(PQ) == 4 &&
      sizeof(PQ) == 12,
    "a class defined under #pragma pack(1) is not a packed TYPE: as a non-POD "
    "member it keeps the typedef alignment");
  return 0;
}
