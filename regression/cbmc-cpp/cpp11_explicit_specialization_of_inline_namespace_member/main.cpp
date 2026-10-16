extern "C" void __CPROVER_assert(bool, const char *);
namespace lib
{
inline namespace v1
{
template <class T>
struct hash
{
  int operator()(const T &) const
  {
    return 0;
  }
};
} // namespace v1
} // namespace lib
struct key
{
  int no;
};
// N5008 [namespace.def.general]/7: a member of an inline namespace can be
// explicitly specialized as though it were a member of the enclosing
// namespace
namespace lib
{
template <>
struct hash<key>
{
  int operator()(const key &k) const
  {
    return k.no;
  }
};
} // namespace lib
int main()
{
  key k{7};
  __CPROVER_assert(lib::hash<key>{}(k) == 7, "specialization selected");
  __CPROVER_assert(lib::v1::hash<key>{}(k) == 7, "same specialization");
  __CPROVER_assert(lib::hash<key>{}(k) == 0, "WRONG (must FAIL)");
  return 0;
}
