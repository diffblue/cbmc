namespace std {
  // cmath
  __inline float abs(float x) __attribute__((nothrow));
  __inline double abs(double x) __attribute__((nothrow));
  __inline long double abs(long double x) __attribute__((nothrow));
}

namespace std {
  extern "C" {
    int abs(int) __attribute__((nothrow)) ;
  }
  extern "C++" { 
    inline long abs(long n) __attribute__((nothrow));
    inline long long abs(long long n) __attribute__((nothrow));
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

