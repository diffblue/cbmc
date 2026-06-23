// N5008 [temp.arg]/2 + [temp.deduct]/8: a template argument of the wrong kind
// (a non-type argument supplied for a type parameter) is a substitution
// failure that, during overload resolution, removes only that candidate from
// the overload set -- it is not a hard error.
//
// This is the shape of std::get<0>(tuple<...>): the by-index
// `get<size_t, _Ts...>(tuple<_Ts...>&)` and the by-type
// `get<_Tp, _Up>(pair<_Tp,_Up>&&)` are both visible.  Matching the explicit
// `<0>` against the by-type overload binds the literal `0` to the *type*
// parameter `_Tp`, which is ill-formed for that candidate.  Per the standard
// this only removes the by-type candidate; the by-index candidate is selected.
//
// CBMC previously reported this kind mismatch as a hard "expected type, but
// got expression" error that aborted resolution of the whole overload set, so
// the viable by-index candidate was never selected and `get<0>(t)` (and every
// statement after it) was silently dropped -- a vacuous result.  Fixed by
// catching the (now typed) mismatch in `apply_template_args` and skipping only
// that candidate.
//
// `get<0>(t)` selects the by-index overload and returns 42; assertion 1 must
// SUCCEED.  Assertion 2 (a wrong value) must FAIL, proving non-vacuity.

template <typename...>
struct tuple
{
  int v;
};

template <typename, typename>
struct pair
{
};

// by-index overload (first template parameter is a non-type size_t)
template <unsigned long _I, typename... _Ts>
int get(tuple<_Ts...> &__t)
{
  return __t.v;
}

// by-type overload (first template parameter is a type) -- not viable for an
// explicit non-type argument `<0>`, must be silently discarded
template <typename _Tp, typename _Up>
_Tp &&get(pair<_Tp, _Up> &&__p);

int main()
{
  tuple<int> t;
  t.v = 42;
  int a = get<0>(t);
  __CPROVER_assert(
    a == 42, "by-index tuple get<0> selected over by-type pair get");
  __CPROVER_assert(a == 999, "WRONG (must FAIL)");
  return 0;
}
