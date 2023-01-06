#include <assert.h>

struct _12817932758143517076
{
  unsigned char _0;
};

struct _14237415465709481864_union__Err
{
  unsigned char cap;
};

union _14237415465709481864_union
{
  struct _12817932758143517076 value;
  struct _14237415465709481864_union__Err Err;
};

void main(void)
{
  unsigned int x; // nondet

  // the following is crucial (else pn trivially simplifies to 0)
  unsigned int var_7 = x;
  unsigned int pn = x - var_7;

  unsigned char raw;
  unsigned char mask;
  if(pn == 0)
  {
    raw = 1;
    mask = 0;
  }
  else
    assert(0);

  union _14237415465709481864_union var_11;
  if(mask != 0)
  {
    var_11.Err.cap = 0;
  }
  else
  {
    var_11.value._0 = 1;
    goto bb5;
  }

  // required to make this test fail (before the fix)
  int tmp = 1;

bb5:;
  struct _12817932758143517076 truncated_packet_number = var_11.value;
  unsigned char r = truncated_packet_number._0;
  assert(raw == r);
}
