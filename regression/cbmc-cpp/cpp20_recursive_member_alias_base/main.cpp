// A base-specifier naming a RECURSIVE member alias template
// (libc++'s _OrImpl: `_Result = _OrImpl<sizeof...(_Rest)>::template
// _Result<_First>`, peeling one pack element per step) resolves to an
// empty type: typecheck_compound_bases drops the base silently, the
// class loses its inherited members, and any qualified use
// (contig::value) inside a later template body is a substitution
// failure that silently no-bodies the enclosing instance (sixth layer
// of the vector push_back family; the same machinery underlies
// std::__libcpp_is_contiguous_iterator / _Or / _And).
// The non-recursive shape (cf. [temp.alias]/2 substitution) works.
extern "C" void __CPROVER_assert(bool, const char *);

template <int __v>
struct integral_constant
{
  static const int value = __v;
};

template <int>
struct _OrImpl
{
  template <class _First, class... _Rest>
  using _Result = _OrImpl<sizeof...(_Rest)>::template _Result<_First>;
};

template <>
struct _OrImpl<0>
{
  template <class _Res>
  using _Result = _Res;
};

struct contig : _OrImpl<1>::_Result<integral_constant<0>, int>
{
};

template <class T>
int go(T t)
{
  return t + contig::value;
}

int main()
{
  __CPROVER_assert(go(1) == 1, "through recursive alias base");
}
