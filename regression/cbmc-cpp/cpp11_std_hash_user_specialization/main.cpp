// N5008 [temp.expl.spec]/2 + [unord.hash]: user code makes a type usable as an
// unordered-container key by specializing std::hash for it, written with a
// qualified-id from outside namespace std:
//   template <> struct std::hash<D> { ... };
// The specialization must be selected when std::hash<D> is used.  Here the
// primary std::hash template is only declared (as the library leaves it for
// non-enabled types), so selecting the primary instead of the specialization
// would fail; selecting the specialization yields n + 100.  g++/clang++ agree.
//
// assertion.2 must FAIL, proving assertion.1 is non-vacuous.

extern "C" void __CPROVER_assert(int, const char *);

namespace std
{
template <class T>
struct hash;
} // namespace std

struct D
{
  unsigned n;
};

template <>
struct std::hash<D>
{
  unsigned operator()(const D &d) const
  {
    return d.n + 100;
  }
};

int main()
{
  D a{3};
  std::hash<D> h;
  __CPROVER_assert(h(a) == 103, "std::hash<D> qualified specialization selected");
  __CPROVER_assert(h(a) == 3, "WRONG must FAIL");
  return 0;
}
