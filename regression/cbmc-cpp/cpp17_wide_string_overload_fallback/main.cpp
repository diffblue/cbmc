// Overloads over basic_string<char> and basic_string<wchar_t> called
// with a narrow string literal: only the char overload is viable
// ([over.match.viable]; const char* does not convert to const
// wchar_t*, [conv.ptr]).  CBMC's char-pointer -> basic_string
// conversion fallback (cpp_typecheck_conversions.cpp) used to fire for
// the wchar_t instantiation as well -- the class NAME is the trigger
// -- and its speculative constructor call leaked "invalid implicit
// conversion from 'const char *' to 'const int *'" diagnostics that
// failed the run even though the exception was swallowed.  Fixed
// 2026-07-22 (element-width gate + diagnostic rollback); this is the
// minimal guard for std::stoll("...") from <string>.
extern "C" void __CPROVER_assert(bool, const char *);

template <typename _CharT>
struct basic_string
{
  basic_string(const _CharT *, long, int = int())
  {
  }
  basic_string(const _CharT *)
  {
  }
};

long stoll(basic_string<char>)
{
  return 1;
}
long stoll(basic_string<wchar_t>)
{
  return 2;
}

int main()
{
  __CPROVER_assert(stoll("41") == 1, "narrow literal picks char overload");
  return 0;
}
