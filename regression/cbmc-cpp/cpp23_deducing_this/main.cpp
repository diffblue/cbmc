// C++23 deducing this
struct S
{
  int x;
  int get(this const S &self)
  {
    return self.x;
  }
};

int main()
{
  S s{42};
  __CPROVER_assert(s.get() == 42, "deducing this");
}
