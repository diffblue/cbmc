// Calling operator() on a temporary object
struct F
{
  int operator()(int x) const
  {
    return x;
  }
};

int main()
{
  int r = F()(42);
  __CPROVER_assert(r == 42, "operator() on temporary");
}
