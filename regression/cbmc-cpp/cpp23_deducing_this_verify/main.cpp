// C++23 deducing this
struct S
{
  int x;
  int get(this S self)
  {
    return self.x;
  }
};
int main()
{
  S s;
  s.x = 42;
  int r = s.get();
  __CPROVER_assert(r == 42, "deducing this");
  return 0;
}
