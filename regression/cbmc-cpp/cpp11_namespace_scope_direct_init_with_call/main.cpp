extern "C" void __CPROVER_assert(bool, const char *);
static int calls;
static bool rd()
{
  ++calls;
  return true;
}
struct holder
{
  int v;
  holder(int x) : v(x)
  {
  }
};
static int seven()
{
  return 7;
}
// [dcl.ambig.res]/1 applies only when the name in parentheses is a type: rd
// and seven are functions, so these define variables initialised with the
// results of the calls
bool b(rd());
holder h(seven());
struct T
{
};
int takes(T());
int takes(T (*f)())
{
  return f == nullptr ? 1 : 2;
}
int main()
{
  __CPROVER_assert(b && calls == 1, "bool from a call");
  __CPROVER_assert(h.v == 7, "class from a call");
  // here T is a type: takes is a function
  __CPROVER_assert(takes(nullptr) == 1, "function declaration");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
