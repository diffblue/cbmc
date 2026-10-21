// N5008 [expr.typeid]/1, [type.info]/2: typeid yields the type_info object
// of its type; two of them compare equal iff they denote the same type.
// The shape of libc++'s non-unique ARM RTTI (arm64 Darwin): the name is an
// integer whose most significant bit marks a name that may not be unique;
// unique names compare by value, others by strcmp.
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" int strcmp(const char *, const char *);
namespace std
{
class type_info
{
  typedef unsigned long name_t;
  static const name_t non_unique_bit = 1ul << 63;
  static bool unique(name_t v)
  {
    return !(v & non_unique_bit);
  }
  static const char *to_string(name_t v)
  {
    return reinterpret_cast<const char *>(v & ~non_unique_bit);
  }

public:
  virtual ~type_info();
  bool operator==(const type_info &other) const noexcept
  {
    if(__type_name == other.__type_name)
      return true;
    if(unique(__type_name) || unique(other.__type_name))
      return false;
    return strcmp(to_string(__type_name), to_string(other.__type_name)) == 0;
  }
  name_t __type_name;
};
} // namespace std
int main()
{
  __CPROVER_assert(typeid(int) == typeid(int), "same type");
  __CPROVER_assert(!(typeid(int) == typeid(char)), "different types");
  __CPROVER_assert(typeid(int) == typeid(char), "WRONG (must FAIL)");
  return 0;
}
