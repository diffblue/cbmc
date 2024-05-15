template <class _Tp, _Tp __v>
struct integral_constant
{
  static const _Tp value = __v;
};

template <class _Tp, _Tp __v>
const _Tp integral_constant<_Tp, __v>::value;

typedef integral_constant<bool, true> true_type;

int main(int argc, char *argv[])
{
}
