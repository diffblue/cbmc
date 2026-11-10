extern "C" void __CPROVER_assert(bool, const char *);
enum class flags
{
  a = 1,
  b = 2
};
// as main.cpp, for a scoped enumeration hidden by a parameter (libc++'s
// __format_spec::__validate_second(__flags __flags), `__flags::__second')
bool has_b(flags flags)
{
  return (static_cast<int>(flags) & static_cast<int>(flags::b)) != 0;
}
int main()
{
  __CPROVER_assert(has_b(flags::b), "enumeration hidden by parameter");
  __CPROVER_assert(!has_b(flags::b), "WRONG (must FAIL)");
}
