extern "C" void __CPROVER_assert(bool, const char *);

template <bool>
struct _IfImpl
{
  static const int tag = 1;
};

template <bool _Cond, class, class>
using _If = _IfImpl<_Cond>;

template <bool _Bp, class _ElseRes>
struct conditional
{
  using type = _If<_Bp, int, _ElseRes>;
};

// The alias's parameter `_If` shares its short name with the
// template-name used inside conditional's member alias.
template <bool _Bp, class _If, class _Then>
using __conditional_t = typename conditional<_Bp, _Then>::type;

struct S
{
  int f;
};

int main()
{
  __CPROVER_assert(
    __conditional_t<true, S, void>::tag == 1,
    "caller type-parameter must not hijack the template-name");
  return 0;
}
