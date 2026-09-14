extern "C" void __CPROVER_assert(bool, const char *);
struct pairt
{
  int first;
  int second;
};
struct itert
{
  pairt *p;
  pairt &operator*()
  {
    return *p;
  }
  void operator++()
  {
    ++p;
  }
};
bool operator!=(itert a, itert b)
{
  return a.p != b.p;
}
struct ranget
{
  pairt data[2];
  itert begin()
  {
    return itert{data};
  }
  itert end()
  {
    return itert{data + 2};
  }
};
int main()
{
  ranget r{{{1, 2}, {3, 4}}};
  int sum = 0;
  // N5008 [stmt.ranged]/1 + [dcl.struct.bind]: value bindings
  for(auto [a, b] : r)
    sum += a + b;
  __CPROVER_assert(sum == 10, "value bindings sum");
  // reference bindings mutate through the range
  for(auto &[a, b] : r)
    a = b;
  __CPROVER_assert(r.data[0].first == 2 && r.data[1].first == 4, "ref bindings wrote through");
  return 0;
}
