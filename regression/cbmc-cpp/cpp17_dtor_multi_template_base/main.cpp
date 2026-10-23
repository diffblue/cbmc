// Regression for [class.dtor] base-subobject destructor lookup when a
// class derives from two specializations of the same template.
//
// Mirrors the libstdc++ pattern that triggered dog-food failures in
// `_Hashtable_base` (used by `std::unordered_map`):
//
//   template<int _Nm, typename _Tp,
//            bool __use_ebo = !__is_final(_Tp) && __is_empty(_Tp)>
//     struct _Hashtable_ebo_helper;
//
//   template<typename _Key, ...>
//     struct _Hash_code_base
//       : private _Hashtable_ebo_helper<1, _Hash>,
//         private _Hashtable_ebo_helper<2, _RangeHash>
//     { ... };
//
// The compiler-generated destructor of the derived class iterates the
// base subobjects and emits `(*(Base*)this).~Base()` for each.  Before
// the fix, `dereference_exprt{this_expr, base_type}` would have its
// type overwritten to the DERIVED class type by
// `c_typecheck_baset::typecheck_expr_dereference`, which sets the
// dereference type to the pointer's base type (struct Derived).
// Subsequent unqualified lookup of `~Base` from the derived class
// scope would then walk every base subobject's secondary scope and
// match every base whose `base_name` equals `~Base` — for two
// specializations of the same template, both would match because
// they share the same unqualified `base_name` (e.g.,
// `~_Hashtable_ebo_helper`).  The result was the spurious diagnostic
//
//   symbol '~Base' does not uniquely resolve:
//     member destructor .~Base(struct Base *)
//     member destructor .~Base(struct Base *)
//
// (with two candidates whose printed signatures look identical because
// the template-arg suffix is stripped from the displayed type).
//
// The fix casts `this_expr` to `Base*` before dereferencing and marks
// the cast as already-type-checked, so the dereference's type stays
// pinned to the specific base subobject's class.

template <int N, typename T>
struct ebo
{
  ebo()
  {
  }
  ~ebo()
  {
  }
};

struct empty1
{
};
struct empty2
{
};

// Class derived from two specializations of `ebo` whose unqualified
// `~ebo` destructor base_names are identical but whose template args
// differ.  Provide an explicit default constructor so the implicit
// destructor (which our fix targets) is generated and exercised
// without triggering the separate constructor-lookup ambiguity.
struct base1 : private ebo<1, empty1>, private ebo<2, empty1>
{
  base1() : ebo<1, empty1>{}, ebo<2, empty1>{}
  {
  }
};

// Variant that mirrors libstdc++'s `_Hashtable_base` slightly more
// closely: different second-arg specializations.
struct base2 : private ebo<1, empty1>, private ebo<2, empty2>
{
  base2() : ebo<1, empty1>{}, ebo<2, empty2>{}
  {
  }
};

int main()
{
  base1 b1;
  base2 b2;
  (void)b1;
  (void)b2;
  return 0;
}
