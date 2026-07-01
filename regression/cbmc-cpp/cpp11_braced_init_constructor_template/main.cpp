// N5008 [over.match.list]/2.2 with [over.match.ctor] and [temp.deduct]: when a
// class is list-initialized from a braced-init-list and no viable
// initializer-list constructor applies, the braced-init-list is treated as the
// argument list for the class's constructors -- and constructor *templates*
// participate in that overload resolution just like ordinary constructors.
//
// std::pair's element-wise constructor is a template, so constructing a pair
// from `{a, b}` (as in `map.insert({k, v})`) exercises exactly this path.  CBMC
// previously did not consider constructor templates when checking whether a
// braced-init-list could initialize a class parameter, so such a call was
// rejected with "found no match for symbol '...'".  This was the root cause of
// the dominant "no match for symbol 'insert'" cluster seen when compiling
// CBMC's own std::unordered_map uses.
//
// The failure is not specific to member calls (a free function is affected the
// same way); a member call is used here as the representative reproducer.
// assertion.2 must FAIL, proving the test is not vacuous.

extern "C" void __CPROVER_assert(int, const char *);

int g_a = 0;
int g_b = 0;

struct pair
{
  int a;
  int b;
  // Element-wise constructor *template* (mirrors std::pair's forwarding ctor).
  template <int = 0>
  pair(int x, int y) : a(x), b(y)
  {
  }
};

struct Map
{
  void insert(pair p)
  {
    g_a = p.a;
    g_b = p.b;
  }
};

int main()
{
  Map m;
  m.insert({5, 9}); // braced-init-list -> pair via the constructor template
  __CPROVER_assert(
    g_a == 5 && g_b == 9, "braced-init-list initializes class via ctor template");
  __CPROVER_assert(g_a != 5, "WRONG must FAIL");
  return 0;
}
