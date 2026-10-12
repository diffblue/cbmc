// N5008 [class.dtor]/13, [class.union.general]/1, [class.union.anon]/1: a
// destructor destroys only non-variant members.  The members of a union,
// named or anonymous, are variant members; a user-provided union or class
// destructor used to destroy them anyway (libc++'s ~__hash_node() {} then
// called the deleted ~__hash_value_type of std::unordered_map).
extern "C" void __CPROVER_assert(bool, const char *);
int destroyed = 0;
struct V
{
  int x;
  ~V()
  {
    ++destroyed;
  }
};
struct N
{
  union
  {
    V v;
  };
  N()
  {
  }
  ~N()
  {
  }
};
union U
{
  V v;
  U()
  {
  }
  ~U()
  {
  }
};
int main()
{
  {
    N n;
  }
  __CPROVER_assert(destroyed == 0, "anonymous union member not destroyed");
  {
    U u;
  }
  __CPROVER_assert(destroyed == 0, "union member not destroyed");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
