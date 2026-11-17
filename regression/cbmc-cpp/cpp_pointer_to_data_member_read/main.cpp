extern "C" void __CPROVER_assert(bool, const char *);
struct s
{
  int x = 5;
  int y = 7;
};
struct u
{
  int x = 5;
  int s::*pm = &s::y;
};
int main()
{
  s v;
  int s::*pm = &s::y;
  __CPROVER_assert(v.*pm == 7, "read through a pointer to data member");
  u w;
  __CPROVER_assert(w.x == 5 && v.*(w.pm) == 7, "pointer to member as NSDMI");
  __CPROVER_assert(v.*pm == 5, "WRONG (must FAIL)");
}
