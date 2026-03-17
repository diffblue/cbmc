// Structured bindings parse but are treated as skip for now
struct S
{
  int a;
  double b;
};
int main()
{
  S s{42, 3.14};
  auto [x, y] = s;
  auto &[p, q] = s;
  return 0;
}
