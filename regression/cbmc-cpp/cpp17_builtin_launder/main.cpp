extern "C" void __CPROVER_assert(bool, const char *);
struct pod
{
  int v;
};
int main()
{
  // GCC/Clang builtin behind std::launder ([ptr.launder]): returns its
  // argument
  pod p{3};
  pod *q = __builtin_launder(&p);
  __CPROVER_assert(q == &p && q->v == 3, "launder yields the same pointer");
  __CPROVER_assert(q->v == 4, "WRONG (must FAIL)");
}
