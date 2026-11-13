extern "C" void __CPROVER_assert(bool, const char *);
// libc++ 23's basic_string representation: a union whose variant member
// `__long' has a defaulted default constructor
struct Long
{
  Long() = default;
  long cap;
  char *data;
};
struct Short
{
  char size;
  char data[15];
};
union Rep
{
  Short s;
  Long l;
};
struct String
{
  Rep rep;
  void reset()
  {
    rep = Rep();
  }
  int size() const
  {
    return rep.s.size;
  }
};
int main()
{
  String str;
  str.rep.s.size = 5;
  __CPROVER_assert(str.size() == 5, "short size set");
  str.reset();
  __CPROVER_assert(str.size() == 0, "Rep(): the union is value-initialized");
  Rep *heap = new Rep();
  __CPROVER_assert(heap->s.size == 0, "new Rep()");
  Rep braces{};
  __CPROVER_assert(braces.l.cap == 0, "Rep braces{}");
  __CPROVER_assert(str.size() == 5, "WRONG (must FAIL)");
}
