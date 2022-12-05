#ifdef _MSC_VER
// No _Static_assert in Visual Studio
#  define _Static_assert(condition, message) static_assert(condition, message)
#endif

struct S
{
  struct
  {
    int : 1;
#ifndef _MSC_VER
    int;
#endif
    int named;
  };
};

_Static_assert(sizeof(struct S) == sizeof(int) * 2, "ignore int;");

struct S s = {.named = 0};

struct S1
{
  struct S2
  {
    int : 1;
    int named;
  };
};

#ifdef _MSC_VER
_Static_assert(sizeof(struct S1) == sizeof(int) * 2, "");
#else
_Static_assert(sizeof(struct S1) == 0, "");
#endif

int main()
{
}
