// N5008 [unique.ptr.single.ctor], [unique.ptr.single.asgn]: unique_ptr move
// construction and move assignment transfer ownership and null the source.
// Exercises the whole libstdc++ chain -- unique_ptr's defaulted move members,
// __uniq_ptr_data's defaulted move members over the user-defined
// __uniq_ptr_impl move operations, and std::tuple's EBO _Tuple_impl /
// _Head_base hierarchy underneath ([class.copy.ctor]/15,
// [class.copy.assign]/12, [class.inhctor.init]).  Runtime-verified against
// g++ and clang++.

#include <memory>

extern "C" void __CPROVER_assert(int, const char *);

struct C
{
  int v;
  explicit C(int x) : v(x)
  {
  }
};

int main()
{
  std::unique_ptr<C> p;
  __CPROVER_assert(p.get() == nullptr, "default-constructed is null");

  p = std::unique_ptr<C>(new C(5));
  __CPROVER_assert(p->v == 5, "move assignment from a temporary");

  std::unique_ptr<C> q(std::move(p));
  __CPROVER_assert(q->v == 5, "move construction transfers the value");
  __CPROVER_assert(p.get() == nullptr, "move construction nulls the source");

  std::unique_ptr<C> r;
  r = std::move(q);
  __CPROVER_assert(r->v == 5, "move assignment transfers the value");
  __CPROVER_assert(q.get() == nullptr, "move assignment nulls the source");

  return 0;
}
