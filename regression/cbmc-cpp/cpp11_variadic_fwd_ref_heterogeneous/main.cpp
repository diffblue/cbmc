// N5008 [temp.deduct.call]/1-4 + [temp.variadic]/4: a variadic function
// template with a forwarding-reference parameter pack `A&&...` deduces each
// pack element independently; the deduced elements may have DIFFERENT types.
// The function then has one parameter per deduced element, each with its own
// (possibly distinct) type.
//
// CBMC expanded the pack into `pack_size` copies of the FIRST element's
// parameter, which is only correct for a homogeneous pack.  For a
// forwarding-reference pack that made every parameter the first element's
// reference type, so a later argument of a different type could not bind
// (there is no implicit conversion to a reference of an unrelated type) and
// the call was wrongly rejected with "found no match".

extern "C" void __CPROVER_assert(int, const char *);

template <typename... A>
int count(A &&...a)
{
  return sizeof...(a);
}

struct S
{
};
struct R
{
};

int main()
{
  int i = 3;
  double d = 4.5;
  S s;
  R r;

  // Heterogeneous forwarding-reference packs must deduce and instantiate.
  __CPROVER_assert(count(i, d) == 2, "heterogeneous int,double pack size 2");
  __CPROVER_assert(count(s, r, i) == 3, "heterogeneous S,R,int pack size 3");

  // Non-vacuity guard: a deliberately wrong property that must FAIL.
  __CPROVER_assert(count(i, d) == 9, "WRONG: must fail");

  return 0;
}
