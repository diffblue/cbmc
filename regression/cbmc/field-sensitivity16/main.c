#include <assert.h>

struct _17626587426415757163
{
  unsigned long int cap;
};

struct _14237415465709481864_union__Err
{
  struct _17626587426415757163 _0;
};

struct _12817932758143517076_union__U8
{
  unsigned char _0;
};

union _12817932758143517076_union_
{
  struct _12817932758143517076_union__U8 U8;
};

struct _2123760316064833246_
{
  union _12817932758143517076_union_ cases;
};

union _14237415465709481864_union
{
  struct _2123760316064833246_ Ok;
  struct _14237415465709481864_union__Err Err;
};

void main(void)
{
  unsigned int x; // nondet

  // the following is crucial (else pn trivially simplifies to 0)
  unsigned int var_7 = x;
  unsigned int pn = x - var_7;

  unsigned char mask;
  if(pn == 0)
    mask = 0;
  else
    assert(0);

  union _14237415465709481864_union var_11;
  if(mask != 0)
  {
    assert(0);
    var_11.Err._0.cap = 0;
  }
  else
  {
    var_11.Ok.cases.U8._0 = 1;
    goto bb5;
  }

  // keep this
  int tmp = 1;
bb5:;

  struct _2123760316064833246_ truncated_packet_number = var_11.Ok;
  assert(1 == var_11.Ok.cases.U8._0);
  assert(1 == truncated_packet_number.cases.U8._0);
}
