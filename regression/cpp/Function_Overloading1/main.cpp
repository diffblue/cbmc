#ifdef __GNUC__
#define NOTHROW __attribute__((nothrow))
#else
#define NOTHROW
#endif

namespace std {
  // cmath
  __inline float abs(float x) NOTHROW;
  __inline double abs(double x) NOTHROW;
  __inline long double abs(long double x) NOTHROW;
}

namespace std {
  extern "C" {
    int abs(int) NOTHROW ;
  }
  extern "C++" {
    inline long abs(long n) NOTHROW;
    inline long long abs(long long n) NOTHROW;
  }
}

using std::abs;

int main(int argc, char* argv[])
{
  unsigned short y;
  int x;
  if(abs(y-x)>0)
    return 1;
  return 0;
}
