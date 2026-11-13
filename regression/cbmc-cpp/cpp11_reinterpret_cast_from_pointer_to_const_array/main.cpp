// N5008 [expr.reinterpret.cast]/2, /7, [expr.const.cast]/6: converting a
// pointer to an array of const unsigned char to a pointer to const T does
// not cast away constness (the array's elements are const, [basic.type.
// qualifier]/3).  libstdc++ 16's <any> reads its in-place buffer this way:
// `reinterpret_cast<const _Tp *>(&__any->_M_storage._M_buffer)'.
extern "C" void __CPROVER_assert(bool, const char *);
struct storage
{
  alignas(int) unsigned char buffer[sizeof(int)];
};
template <class T>
const T *access(const storage &s)
{
  return reinterpret_cast<const T *>(&s.buffer);
}
int main()
{
  storage s;
  const int v = 42;
  const unsigned char *bytes = reinterpret_cast<const unsigned char *>(&v);
  for(unsigned i = 0; i < sizeof v; ++i)
    s.buffer[i] = bytes[i];
  const unsigned char(*p)[sizeof(int)] = &s.buffer;
  __CPROVER_assert(
    *access<int>(s) == 42 && *reinterpret_cast<const int *>(p) == 42,
    "read through the cast");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
