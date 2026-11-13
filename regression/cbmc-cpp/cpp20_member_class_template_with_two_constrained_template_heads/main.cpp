// N5008 [temp.mem]/1, [temp.constr.decl]/3: a member class template of a
// constrained class template defined outside the class has two
// template-heads, each with a requires-clause; the associated constraints
// are their conjunction.  Guards the merge of nested template-heads after a
// requires-clause (both clauses parsed: the parser's count-only fallback
// for an unparseable clause is not reached by any valid clause known).
// g++ 13 accepts the program; clang++ 18 and 20 reject it ("requires
// clause differs in template redeclaration"), although the clauses are the
// same as in the declarations ([temp.over.link]/6).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept small = sizeof(T) <= 4;
template <class V>
  requires small<V>
struct view
{
  template <class U>
    requires small<U>
  struct box;
  template <class U>
    requires requires(U u) { u + 1; }
  struct num;
};
template <class V>
  requires small<V>
template <class U>
  requires small<U>
struct view<V>::box
{
  U u;
  V v;
  int sum() const
  {
    return u + v;
  }
};
template <class V>
  requires small<V>
template <class U>
  requires requires(U u) { u + 1; }
struct view<V>::num
{
  U u;
  int next() const
  {
    return u + 1;
  }
};
int main()
{
  view<int>::box<char> b{2, 40};
  view<short>::num<int> n{6};
  __CPROVER_assert(b.sum() == 42, "both template-heads constrained");
  __CPROVER_assert(n.next() == 7, "inner requires-expression");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
