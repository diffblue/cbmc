// N5008 [stmt.if]: an if statement with an init-statement.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int r = 0;
  if(int x = 3; x > 2)
    r = x;
  __CPROVER_assert(r == 3, "if with an initializer");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
