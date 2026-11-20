// Regression for [class.base.init] base-subobject constructor lookup
// when a class derives from two specializations of the same template.
//
// Mirrors the libstdc++ pattern that motivates this fix:
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
// The compiler-generated default constructor of the derived class is
// produced by `cpp_typecheckt::full_member_initialization`, which
// iterates over each base subobject and emits a synthetic
// `member_initializer` whose name is the unqualified base
// `base_name`.  When two bases are different specializations of the
// same template, the cpp_name has the same `base_name` for each
// (e.g., `ebo`).  `typecheck_member_initializer` then resolves the
// unqualified name from the constructor's class scope and finds two
// constructors — one per specialization — surfacing as the spurious
// diagnostic
//
//   symbol 'X' does not uniquely resolve:
//     symbol constructor X(struct X *)
//     symbol constructor X(struct X *)
//
// The fix records the specific base subobject's `struct_tag` type on
// the synthetic member-initializer (`#base_type`), and
// `typecheck_member_initializer` scopes the resolve to that struct
// when present.

template <int N, typename T>
struct ebo
{
  ebo()
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
// constructor `base_name` is `ebo` for both bases.
struct base1 : private ebo<1, empty1>, private ebo<2, empty1>
{
};

// Variant: different second-arg specializations.
struct base2 : private ebo<1, empty1>, private ebo<2, empty2>
{
};

int main()
{
  base1 b1;
  base2 b2;
  (void)b1;
  (void)b2;
  return 0;
}
