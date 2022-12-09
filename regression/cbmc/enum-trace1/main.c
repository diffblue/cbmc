#include <assert.h>

enum ENUM
{
  E1,
  E2,
  E3
};

typedef enum ENUMT
{
  T1,
  T2,
  T3
} enum_t;

void test(enum ENUM e, enum_t t)
{
  // ensure sane input values
  __CPROVER_assume(__CPROVER_enum_is_in_range(e));
  __CPROVER_assume(__CPROVER_enum_is_in_range(t));
  enum ENUM ee = e;
  enum_t tt = t;

  assert(ee != tt);
}
