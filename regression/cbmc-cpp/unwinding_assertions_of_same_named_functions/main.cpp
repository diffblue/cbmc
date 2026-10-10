// Two functions named `fill' in different namespaces each have a loop.
// With --unwind 2 both unwinding assertions fail, and each needs a result of
// its own; both were given the property id `fill.unwind.0' (the id is built
// from the unqualified function name), so only a::fill's result was
// reported.
namespace a
{
int fill(int n)
{
  int s = 0;
  for(int i = 0; i < n; ++i)
    s += i;
  return s;
}
} // namespace a
namespace b
{
int fill(int n)
{
  int s = 0;
  for(int i = 0; i < n; ++i)
    s += 2;
  return s;
}
} // namespace b
int main()
{
  return a::fill(3) + b::fill(3);
}
