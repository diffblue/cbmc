// N5008 [string.conversions]/1-3: stoi ... stoull of a wstring call wcstol
// ... wcstoull.  libstdc++ calls those of the C library, which had no
// models ("no body for callee wcstol"); libc++'s are defined in its
// compiled library, whose models read the string as `const char *' and did
// not type-check for wstring (the overloads stayed without a body).
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::wstring w = L"42x";
  std::size_t idx = 0;
  int v = std::stoi(w, &idx);
  __CPROVER_assert(v == 42 && idx == 2, "stoi");
  __CPROVER_assert(std::stoll(std::wstring(L"-7")) == -7, "stoll");
  __CPROVER_assert(
    std::stoul(std::wstring(L"ff"), nullptr, 16) == 255, "stoul");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
