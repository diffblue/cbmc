// Two functions named `fill' in different namespaces each have a loop.
// With --unwind 2 both unwinding assertions fail, and each needs a result of
// its own; both were given the property id `fill.unwind.0' (the id was built
// from the unqualified function name of the source location), so only one
// result was reported.  The id now names the goto function, as the loop's
// identifier (--show-loops, --unwindset) does.
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
int nondet_int();

int main()
{
  // separate paths: a failed unwinding assertion assumes the loop exited,
  // which makes the rest of its path infeasible
  if(nondet_int())
    return a::fill(3);
  return b::fill(3);
}
