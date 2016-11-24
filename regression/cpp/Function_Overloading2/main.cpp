namespace std {
  extern "C" {
    double fabs(double) __attribute__((nothrow)) ;
  }

  __inline float fabs(float x) __attribute__((nothrow));
  __inline long double fabs(long double x) __attribute__((nothrow));

  /* original code from CodeWarrior */
  template <class _T>
    struct __msl_is_integral {static const bool value = false;};
  template <>
    struct __msl_is_integral<unsigned long> {static const bool value = true;};

  template <bool, class _T = void>
    struct __msl_enable_if {};
  template <class _T>
    struct __msl_enable_if<true, _T> {typedef _T type;};

  template <class _A1>
    inline typename __msl_enable_if<__msl_is_integral<_A1>::value, double>::type fabs(_A1 x) {return fabs((double)x);}
}

using std::fabs;

int main(int argc, char* argv[])
{
  unsigned long x;
  if(fabs(x) >= 50)
  return 0;
}

