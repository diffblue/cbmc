// Variable templates used in constexpr class members
typedef long intmax_t;

template <intmax_t _Xp>
inline const intmax_t my_abs = _Xp < 0 ? -_Xp : _Xp;

template <intmax_t _Xp, intmax_t _Yp>
inline const intmax_t my_gcd = my_gcd<_Yp, _Xp % _Yp>;

template <intmax_t _Xp>
inline const intmax_t my_gcd<_Xp, 0> = _Xp;

template <intmax_t _Num, intmax_t _Den>
struct ratio
{
  static constexpr intmax_t na = my_abs<_Num>;
  static constexpr intmax_t da = my_abs<_Den>;
  static constexpr intmax_t g = my_gcd<na, da>;
  static constexpr intmax_t num = na / g;
  static constexpr intmax_t den = da / g;
};

typedef ratio<1, 1000000000000000000> atto;

int main()
{
  return atto::num;
}
