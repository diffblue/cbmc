// N5008 [stmt.ranged]/1, [dcl.type.auto.deduct]/2: in `for(auto *n : r)'
// the placeholder is deduced from the element with the pointer of the
// declarator peeled -- auto = node, n is a node *.  The for-range
// declaration reached the deduction still in parsed form (a
// frontend_pointer), the pointer was not peeled, n became a node ** and
// `n->ident' failed ("member operator requires struct/union type ... but
// got 'struct node *'"; CBMC's own `for(auto *id : id_set)' over
// cpp_scopet::id_sett, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct node
{
  int ident;
};
struct it
{
  node *const *p;
  node *const &operator*() const
  {
    return *p;
  }
  it &operator++()
  {
    ++p;
    return *this;
  }
  bool operator!=(const it &o) const
  {
    return p != o.p;
  }
};
struct range
{
  node *arr[2];
  it begin() const
  {
    return it{arr};
  }
  it end() const
  {
    return it{arr + 2};
  }
};
int main()
{
  node a{1}, b{2};
  range r{{&a, &b}};
  int sum = 0;
  for(auto *n : r)
    sum += n->ident;
  for(node *n : r)
    sum += n->ident;
  for(auto n : r)
    sum += n->ident;
  __CPROVER_assert(
    sum == 9, "auto * from a const-reference-returning iterator");
  node *arr[2] = {&a, &b};
  int s2 = 0;
  for(auto *n : arr)
    s2 += n->ident;
  for(const auto *n : arr)
    s2 += n->ident;
  __CPROVER_assert(s2 == 6, "auto * over an array of pointers");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
