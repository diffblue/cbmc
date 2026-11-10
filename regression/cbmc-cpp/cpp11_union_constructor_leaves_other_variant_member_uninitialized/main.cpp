extern "C" void __CPROVER_assert(bool, const char *);
// an element type whose default constructor does not exist: it must not be
// needed by a union constructor that initializes the OTHER member
struct item
{
  int v;
  item(int x) : v(x)
  {
  }
  ~item()
  {
  }
};
template <class T>
struct temporary_value
{
  // libstdc++'s vector::_Temporary_value::_Storage and optional's
  // _Storage: a union with a trivial byte member and a variant member of
  // class type
  union storage
  {
    constexpr storage() : byte()
    {
    }
    ~storage()
    {
    }
    storage &operator=(const storage &) = delete;
    unsigned char byte;
    T val;
  };
  storage s;
};
int main()
{
  temporary_value<item> t;
  __CPROVER_assert(t.s.byte == 0, "the byte member is value-initialized");
  t.s.byte = 3;
  __CPROVER_assert(t.s.byte == 3, "byte member assigned");
  __CPROVER_assert(t.s.byte == 4, "WRONG (must FAIL)");
}
