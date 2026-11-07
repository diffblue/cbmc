// N5008 [over.sub]: an operator[] with two parameters.
extern "C" void __CPROVER_assert(bool, const char *);
struct M
{
  int operator[](int i, int j) const
  {
    return i * 10 + j;
  }
};
int main()
{
  M m;
  __CPROVER_assert((m[1, 2] == 12), "operator[] with two parameters");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
