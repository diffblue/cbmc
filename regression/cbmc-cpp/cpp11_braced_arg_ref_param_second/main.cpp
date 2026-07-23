// A braced-init-list argument converting to a class via a constructor
// whose REFERENCE parameter is not the first one: `take({2, a})` with
// itemt(int, const valt&) fails "invalid implicit conversion from
// 'struct valt' to 'const struct valt *'" -- the reference binding
// (address-of insertion) is skipped for non-initial constructor
// parameters in the list-initialization path ([over.match.list]
// phase 2, [over.ics.list]/8, [dcl.init.ref]/5).  With the reference
// in the FIRST position (itemt(const valt&, int), `take({a, 2})`) the
// same shape converts fine.  Distilled from
// sharing_mapt::get_delta_view's `delta_view.push_back({k1,
// l1.get_value(), ip2->get_value()})` (util/sharing_map.h); blocks
// the abstract_environment.cpp dog-food TU.
extern "C" void __CPROVER_assert(bool, const char *);

struct valt
{
  int x;
};

struct itemt
{
  itemt(int o, const valt &m) : m(m), other_m(o)
  {
  }
  const valt &m;
  int other_m;
};

int take(itemt it)
{
  return it.m.x + it.other_m;
}

int main()
{
  valt a{1};
  __CPROVER_assert(take({2, a}) == 3, "braced arg binds later ref param");
  return 0;
}
