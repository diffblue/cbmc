// N5008 [expr.spaceship]/8: std::strong_ordering is not predefined; the
// built-in <=> of two ints without a preceding declaration of it (from
// <compare>) is ill-formed.  g++ 13 and clang++ 18 reject this program.
int main()
{
  int a = 1, b = 2;
  return (a <=> b) < 0 ? 0 : 1;
}
