extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
inline constexpr bool is_same_v = __is_same(T, U);
struct sv
{
  const char *p;
  unsigned n;
};
struct str
{
  char buf[16];
  unsigned len;
};
template <class C>
struct codecvt_base
{
  int id;
};
template <class C, class Cvt>
bool __str_codecvt_out_all(const C *f, const C *l, str &out, Cvt &cvt)
{
  out.len = 0;
  for(; f != l; ++f)
    out.buf[out.len++] = static_cast<char>(*f) + cvt.id;
  return true;
}
namespace __detail
{
void __throw_conversion_error();
}
class path
{
public:
  using value_type = char;
  template <class E>
  static auto _S_convert(const E *first, const E *last);
  template <class C>
  struct _Codecvt : codecvt_base<C>
  {
    _Codecvt()
    {
      this->id = 1;
    }
  };
};
template <class E>
auto path::_S_convert(const E *__f, const E *__l)
{
  if constexpr(is_same_v<E, value_type>)
    return sv{__f, static_cast<unsigned>(__l - __f)};
  else
  {
    path::_Codecvt<E> __cvt;
    str __str;
    if(__str_codecvt_out_all(__f, __l, __str, __cvt))
      return __str;
  }
  __detail::__throw_conversion_error();
}
void __detail::__throw_conversion_error()
{
  __CPROVER_assert(false, "unreachable");
}
int main()
{
  const char c[] = "abc";
  sv s = path::_S_convert(c, c + 3);
  __CPROVER_assert(s.n == 3, "char branch");
  const wchar_t w[] = L"de";
  str t = path::_S_convert(w, w + 2);
  __CPROVER_assert(t.len == 2 && t.buf[0] == 'e', "converted branch");
  __CPROVER_assert(t.len == 3, "WRONG (must FAIL)");
}
