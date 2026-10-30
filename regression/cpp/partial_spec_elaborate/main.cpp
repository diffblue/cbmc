// Partial specialization matching during class template elaboration.
// When template arguments are stored as unevaluated expressions (e.g.,
// from base class member references), elaborate_class_template must
// resolve them and match against partial specializations.

template <long _Pn, long _Qn>
struct gcd : gcd<_Qn, (_Pn % _Qn)>
{
};

template <long _Pn>
struct gcd<_Pn, 0>
{
  static const long value = _Pn;
};

template <long _Pn>
struct gcd<0, _Pn>
{
  static const long value = _Pn;
};

template <typename _Tp, _Tp __v>
struct integral_constant
{
  static const _Tp value = __v;
  typedef _Tp value_type;
  typedef integral_constant<_Tp, __v> type;
};

template <long _Pn>
struct __static_abs : integral_constant<long, (_Pn < 0) ? -_Pn : _Pn>
{
};

template <long _Pn, long _Qn>
struct ratio
{
  static const long num =
    __static_abs<_Pn>::value /
    gcd<__static_abs<_Pn>::value, __static_abs<_Qn>::value>::value;
  static const long den =
    __static_abs<_Qn>::value /
    gcd<__static_abs<_Pn>::value, __static_abs<_Qn>::value>::value;
};

ratio<1, 1000> r;

int main()
{
  return 0;
}
