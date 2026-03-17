// C++23 deducing this - member call dispatch
struct S
{
  int val;
  int get(this S self)
  {
    return self.val;
  }
};

int main()
{
  S s;
  s.val = 42;
  int r = s.get();
  __CPROVER_assert(r == 42, "deducing this call");
  return 0;
}
