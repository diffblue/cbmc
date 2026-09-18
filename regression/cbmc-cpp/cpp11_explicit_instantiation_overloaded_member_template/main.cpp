extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.explicit]/4: an explicit instantiation of a member function
// template names ONE of several overloaded templates by its declaration.
// `template renamedt<E, L1> S::rename<L1>(E, int);' with two `rename' member
// templates was rejected: "found no match for symbol 'L1'" (the enumerator
// template argument could not be resolved on the fallback path).
enum levelt { L0 = 0, L1 = 1, L2 = 2 };
template <class T, levelt L> struct renamedt { T value; };
struct E { int t; };
struct S
{
  int calls[3] = {0, 0, 0};
  template <levelt level = L2>
  renamedt<E, level> rename(E expr, int ns);
  template <levelt level = L2>
  void rename(int &type, const char *id, int ns);
  template <levelt level>
  void rename_address(E &expr, int ns);
};
template <levelt level>
renamedt<E, level> S::rename(E expr, int ns) { calls[level] += 1; return renamedt<E, level>{expr}; }
template <levelt level>
void S::rename(int &type, const char *id, int ns) { type += level; calls[level] += 10; }
template <levelt level>
void S::rename_address(E &expr, int ns)
{
  // overloaded member template with explicit non-type template argument
  rename<level>(expr.t, "x", ns);
  E e2 = rename<level>(expr, ns).value;
  expr.t += e2.t;
}
template void S::rename_address<L1>(E &, int);
template renamedt<E, L1> S::rename<L1>(E expr, int ns);
int main()
{
  S s; E e{1};
  s.rename_address<L1>(e, 0);
  __CPROVER_assert(e.t == 4, "rename<level>(type, id, ns) added level=1, then doubled: (1+1)*2");
  __CPROVER_assert(s.calls[1] == 11, "both overloads called once at L1");
  s.rename_address<L0>(e, 0);
  __CPROVER_assert(e.t == 8 && s.calls[0] == 11, "L0");
  int t = 5;
  s.rename(t, "y", 0);
  __CPROVER_assert(t == 7 && s.calls[2] == 10, "default template argument L2");
  return 0;
}
