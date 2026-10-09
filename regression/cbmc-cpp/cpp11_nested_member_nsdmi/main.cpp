// N5008 [class.base.init]/9-10 + [class.default.ctor]/3: a non-static data
// member of class type that is not named by a mem-initializer is
// default-constructed by the enclosing class's (implicit) default constructor;
// if that member's class has a default member initializer (NSDMI), the NSDMI
// must be applied.  This must work transitively (members of members, and
// elements of arrays of such classes) and for objects of both automatic and
// static storage duration.
//
// Independently, C++14 [dcl.init.aggr] still permits NSDMIs in an aggregate, so
// a braced-init-list must continue to aggregate-initialize (list elements to
// the leading members, the NSDMI supplying any member not covered by the list).

extern "C" void __CPROVER_assert(int, const char *);

struct inner
{
  int t = 5;
};

struct outer
{
  inner q; // no initializer -> inner's NSDMI must run
};

struct deep
{
  outer o;
};

struct with_array
{
  inner a[2];
};

struct aggregate_partial
{
  int x;
  int y = 20;
};

outer g_outer; // static storage duration

int main()
{
  outer o;
  __CPROVER_assert(o.q.t == 5, "nested member NSDMI (local)");
  __CPROVER_assert(g_outer.q.t == 5, "nested member NSDMI (global)");

  deep d;
  __CPROVER_assert(d.o.q.t == 5, "two-level nested NSDMI");

  inner arr[3];
  __CPROVER_assert(arr[2].t == 5, "array-of-NSDMI element");

  with_array w;
  __CPROVER_assert(w.a[1].t == 5, "member array-of-NSDMI element");

  // Aggregate initialization must be unaffected: x from the list, y from its
  // NSDMI ([dcl.init.aggr]).
  aggregate_partial ap{7};
  __CPROVER_assert(ap.x == 7, "aggregate list element preserved");
  __CPROVER_assert(ap.y == 20, "aggregate NSDMI for unlisted member preserved");

  // Non-vacuity guard: a deliberately wrong property that must FAIL.  Before
  // the fix the nested member was left unconstructed (o.q.t == 0), so this
  // assertion would have SUCCEEDED -- a false pass.
  __CPROVER_assert(o.q.t == 0, "WRONG: must fail");

  return 0;
}
