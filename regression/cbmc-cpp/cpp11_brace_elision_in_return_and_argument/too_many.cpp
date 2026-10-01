struct IA
{
  int v[2];
  int w;
};
// [dcl.init.aggr]/16: an initializer-clause that does not appertain to an
// element of the aggregate or one of its subaggregates is ill-formed
IA g()
{
  return {1, 2, 3, 4};
}
int main()
{
  return g().w;
}
