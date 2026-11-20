extern "C" void __CPROVER_assert(bool, const char *);
// GCC's __complex__ extension: a braced list of two scalars initializes the
// real and the imaginary part (libstdc++'s complex<float>, `_M_value{ __r,
// __i }' in complex:1354)
struct C
{
  __complex__ float v;
  C(float r = 0.0f, float i = 0.0f) : v{r, i}
  {
  }
};
int main()
{
  C c(1.0f, 2.0f);
  __CPROVER_assert(__real__ c.v == 1.0f && __imag__ c.v == 2.0f, "member");
  __complex__ float w{3.0f, 4.0f};
  __CPROVER_assert(__real__ w == 3.0f && __imag__ w == 4.0f, "variable");
  __CPROVER_assert(__imag__ c.v == 1.0f, "WRONG (must FAIL)");
}
