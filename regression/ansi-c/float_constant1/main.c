#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

// hex-based constants
STATIC_ASSERT(0x1.0p-95f == 2.524355e-29f);

// also with upper case X, P, F
STATIC_ASSERT(0X1.0P-95F == 2.524355e-29f);

#ifdef __GNUC__
_Complex c;
#endif

int main()
{
  // imaginary constants, these are GCC only
  #ifdef __GNUC__
  c=(__extension__ 1.0iF);
  c=(__extension__ 1.0Fi);
  c=(__extension__ 1.0jF);
  c=(__extension__ 1.0j);
  c=(__extension__ 1.0jL);
  c=(__extension__ 1.0il);
  #endif
}
