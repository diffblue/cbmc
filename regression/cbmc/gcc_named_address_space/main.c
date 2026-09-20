// The x86 named-address-space (segment) qualifiers __seg_fs / __seg_gs,
// used by the Linux kernel's per-CPU accessors as BARE type qualifiers
// when the compiler supports named address spaces
// (CONFIG_CC_HAS_NAMED_ADDRESS_SPACES) -- e.g. `typeof(x) __seg_gs *`.
// They denote %fs/%gs segment-relative addressing, irrelevant to
// functional verification, so CBMC ignores the qualifier (the pointed-to
// object is unchanged).
struct s
{
  int x;
};

// plain non-pointer object carrying the qualifier (per-CPU object form)
static int __seg_gs percpu;

int main(void)
{
  struct s obj = {.x = 42};
  struct s __seg_gs *p = (struct s __seg_gs *)&obj;
  struct s __seg_fs *q = (struct s __seg_fs *)&obj;
  __typeof__(struct s __seg_gs) *r = &obj;
  // qualifier *before* the type
  __seg_gs int *s = (__seg_gs int *)&obj.x;
  __CPROVER_assert(p->x == 42, "seg-gs-qualified pointer reads the object");
  __CPROVER_assert(q->x == 42, "seg-fs-qualified pointer reads the object");
  __CPROVER_assert(r->x == 42, "typeof with seg qualifier");
  __CPROVER_assert(*s == 42, "seg qualifier before the type");
  percpu = 7;
  __CPROVER_assert(percpu == 7, "non-pointer seg-qualified object");
  return 0;
}
