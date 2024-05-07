template <typename _Tp>
struct __remove_cvref_t
{
};

template <typename _Tp, typename _Up = __remove_cvref_t<_Tp>>
struct __inv_unwrap
{
};

template <typename...>
struct __or_;

template <bool _Cond, typename _Iftrue, typename _Iffalse>
struct conditional
{
  typedef _Iftrue type;
};

template <typename _B1, typename _B2, typename _B3, typename... _Bn>
struct __or_<_B1, _B2, _B3, _Bn...>
  : public conditional<_B1::value, _B1, __or_<_B2, _B3, _Bn...>>::type
{
};

int main(int argc, char *argv[])
{
  int x = 10 >> 1;
}
