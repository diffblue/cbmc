extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
#include <vector>
struct typet
{
  int t;
};
struct exprt
{
  int kind;
};
struct symbol_exprt : exprt
{
  int id_;
  const int &identifier() const
  {
    return id_;
  }
  void identifier(int v)
  {
    id_ = v;
  }
};
class ssa_exprt;
struct namespacet
{
};
enum levelt
{
  L0 = 0,
  L1 = 1,
  L2 = 3
};
template <typename underlyingt, levelt level>
class renamedt : private underlyingt
{
public:
  static_assert(
    std::is_base_of<exprt, underlyingt>::value ||
      std::is_base_of<typet, underlyingt>::value,
    "underlyingt should inherit from exprt or typet");
  const underlyingt &get() const
  {
    return static_cast<const underlyingt &>(*this);
  }

private:
  // a friend declaration naming ANOTHER specialization of this template
  friend renamedt<ssa_exprt, L0>
  symex_level0(ssa_exprt, const namespacet &, unsigned);
  friend struct symex_level1t;
  explicit renamedt(underlyingt u) : underlyingt(u)
  {
  }
};
// a declaration returning renamedt<ssa_exprt, L0> BY VALUE while ssa_exprt is
// incomplete ([dcl.fct]/12: a complete return type is not required here)
renamedt<ssa_exprt, L0> symex_level0(ssa_exprt, const namespacet &, unsigned);
// names renamedt<ssa_exprt, L0> while ssa_exprt is incomplete
struct symex_level1t
{
  void insert(const renamedt<ssa_exprt, L0> &ssa, int index);
  int last;
};
class ssa_exprt : public symbol_exprt
{
public:
  int level0;
};
// a different specialization is fully used: its friend declaration re-elaborates renamedt<ssa_exprt, L0>
struct target
{
  std::vector<renamedt<exprt, L2>> args;
};
renamedt<ssa_exprt, L0> symex_level0(ssa_exprt s, const namespacet &, unsigned)
{
  return renamedt<ssa_exprt, L0>(s);
}
void symex_level1t::insert(const renamedt<ssa_exprt, L0> &ssa, int index)
{
  last = ssa.get().identifier() + index;
}
int main()
{
  ssa_exprt s;
  s.identifier(7);
  s.level0 = 1;
  s.kind = 2;
  namespacet ns;
  symex_level1t l;
  l.insert(symex_level0(s, ns, 0), 1);
  __CPROVER_assert(
    l.last == 8,
    "specialization re-elaborated from another specialization's friend "
    "declaration");
  return 0;
}
