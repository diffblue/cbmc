// Test that _Complex float and _Complex double are distinct types
// for function overloading purposes.
float my_abs(__complex__ float __z);
double my_abs(__complex__ double __z);
long double my_abs(__complex__ long double __z);

int main()
{
  return 0;
}
