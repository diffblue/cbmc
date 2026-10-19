// N5008 [temp.over.link]/5-6, [temp.constr.decl]: two declarations of a
// class template whose constrained parameters name the same concept are
// declarations of the same template, however the concept is qualified
// (`template <chr C> struct fptr;' then `template <fmt::chr C> struct fptr
// {...}' -- libstdc++ 16's <format> declares __formatter_ptr with `__char'
// and defines it with `__format::__char').  The front end compared the
// spelling and rejected the definition ("template declaration of
// '__formatter_ptr' does not match previous declaration"), so every
// std::format call failed to type-check with gcc 16 (Docker matrix:
// tumbleweed, archlinux).
extern "C" void __CPROVER_assert(bool, const char *);
namespace fmt
{
template <class T, class U>
concept same_as = __is_same(T, U);
template <class C>
concept chr = same_as<C, char> || same_as<C, wchar_t>;
template <chr C>
struct fptr; // declared with the concept named unqualified
} // namespace fmt
namespace fmt
{
template <fmt::chr C>
struct fptr // defined with the same concept, qualified
{
  int width = sizeof(C) * 8;
};
} // namespace fmt
int main()
{
  fmt::fptr<char> p;
  fmt::fptr<wchar_t> q;
  __CPROVER_assert(
    p.width == 8 && q.width == sizeof(wchar_t) * 8,
    "redeclaration with equivalently spelled constraint");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
