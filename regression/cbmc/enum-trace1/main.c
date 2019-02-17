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
  enum ENUM ee = e;
  enum_t tt = t;

  assert(ee != tt);
}
