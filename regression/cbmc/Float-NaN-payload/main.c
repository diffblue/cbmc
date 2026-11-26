#include <assert.h>
#include <math.h>
#include <stdint.h>

union uf
{
  float f;
  uint32_t i;
};

union ud
{
  double d;
  uint64_t i;
};

int main(void)
{
  // A negative quiet NaN with payload 1.
  union uf a;
  a.i = 0xFFC00001u;

  // fabs, negation and copysign only change the sign bit, also for NaNs
  // (IEEE 754-2019, 5.5.1).
  union uf b;
  b.f = fabsf(a.f);
  assert(b.i == 0x7FC00001u);

  union uf c;
  c.f = -a.f;
  assert(c.i == 0x7FC00001u);

  union uf d;
  d.f = copysignf(a.f, 1.0f);
  assert(d.i == 0x7FC00001u);

  // A signalling NaN pattern survives a plain copy.
  union uf s, t;
  s.i = 0x7F800001u;
  t.f = s.f;
  assert(t.i == 0x7F800001u);

  union ud e;
  e.i = 0xFFF8000000000001ull;
  union ud g;
  g.d = fabs(e.d);
  assert(g.i == 0x7FF8000000000001ull);

  // NaNs produced by arithmetic are quiet: the most significant fraction
  // bit is set.
  union uf q;
  q.f = 0.0f / 0.0f;
  assert(isnan(q.f));
  assert((q.i & 0x00400000u) != 0);

  union uf r;
  r.f = a.f + 1.0f;
  assert(isnan(r.f));
  assert((r.i & 0x00400000u) != 0);

  union ud p;
  p.d = 0.0 / 0.0;
  assert(isnan(p.d));
  assert((p.i & 0x0008000000000000ull) != 0);

  union ud w;
  w.d = (double)a.f;
  assert(isnan(w.d));
  assert((w.i & 0x0008000000000000ull) != 0);

  return 0;
}
