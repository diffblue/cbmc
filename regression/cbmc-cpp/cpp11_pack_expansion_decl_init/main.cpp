// N5008 [temp.variadic]/5: in a pack expansion, the k-th generated element
// substitutes the k-th element of EVERY pack the pattern references.  Here
// the pattern `forward<A>(a)` references both the function parameter pack
// `a` AND the template type pack `A`; expanding
// `node z(id, forward<A>(a)...)` (a local-object declaration inside a
// member function template -- the _Rb_tree::_M_emplace_hint_unique
// `_Auto_node __z(*this, std::forward<_Args>(__args)...)` shape) must
// substitute A's k-th deduced type per element.
//
// Was KNOWNBUG: only the function parameter pack was renamed per element;
// the type pack `A` was left whole, so each per-element `forward<A>(a$k)`
// failed deduction against every `forward` overload, the enclosing body's
// conversion was dropped (swallowed for system headers), and the emplace
// call read as nondet.
extern "C" void __CPROVER_assert(int, const char *);

template <typename T>
struct remove_reference
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &>
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &&>
{
  typedef T type;
};

template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}
template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &&__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}

struct pc_t
{
};
struct tup1
{
  int v;
};
struct tup0
{
};

struct node
{
  int val;
  int sum;
  node(int owner, pc_t, tup1 &&t1, const tup0 &) : val(owner), sum(t1.v)
  {
  }
};

struct tree
{
  int id;
  tree() : id(7)
  {
  }
  template <typename... _Args>
  int emplace(_Args &&...__args)
  {
    node __z(id, forward<_Args>(__args)...);
    return __z.val + __z.sum;
  }
};

int main()
{
  tree t;
  pc_t pc;
  tup1 t1{35};
  tup0 t0;
  int r = t.emplace(pc, static_cast<tup1 &&>(t1), t0);
  __CPROVER_assert(r == 42, "decl-initializer pack expansion");
  return 0;
}
