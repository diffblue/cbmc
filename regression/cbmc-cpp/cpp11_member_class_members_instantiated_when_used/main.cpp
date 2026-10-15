// N5008 [temp.inst]/3.1, /4: the members of a member class of a class
// template specialization are instantiated when used, and only then
extern "C" void __CPROVER_assert(bool, const char *);
int destroyed = 0;
struct traits
{
  template <class U>
  static void destroy(U *p)
  {
    p->~U();
    ++destroyed;
  }
};
template <class T>
struct vec
{
  int size = 0;
  struct temporary
  {
    T value;
    // libstdc++'s vector<_Tp>::_Temporary_value: ill-formed for an
    // incomplete T, so it must not be instantiated for vec<block>
    void release()
    {
      traits::destroy(&value);
    }
    int get() const
    {
      return value + 1;
    }
  };
};
struct block;
vec<block> blocks;
struct block
{
  int n;
};
int main()
{
  __CPROVER_assert(blocks.size == 0, "unused members not instantiated");
  vec<int>::temporary t{4};
  __CPROVER_assert(t.get() == 5, "used member instantiated");
  t.release();
  __CPROVER_assert(destroyed == 1, "and its callee");
  __CPROVER_assert(destroyed == 0, "WRONG (must FAIL)");
}
