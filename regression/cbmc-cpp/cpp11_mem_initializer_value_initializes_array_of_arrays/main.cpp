extern "C" void __CPROVER_assert(bool, const char *);
template <class E>
struct table
{
  E data[4][2];
  // N5008 [class.base.init]/7, [dcl.init.list]/3.11: `data{}'
  // value-initializes the array member, here zero-initializing each element
  table() : data{}
  {
    data[3][1] = 7;
  }
};
struct flat
{
  int data[3];
  flat() : data{}
  {
  }
};
int main()
{
  table<char> t;
  flat f;
  __CPROVER_assert(
    t.data[0][0] == 0 && t.data[2][1] == 0 && t.data[3][1] == 7,
    "two-dimensional array member");
  __CPROVER_assert(f.data[2] == 0, "one-dimensional array member");
  __CPROVER_assert(t.data[3][1] == 0, "WRONG (must FAIL)");
  return 0;
}
