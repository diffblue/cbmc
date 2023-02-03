// Use a forward declaration instead of including math.h to demonstrate a bugfix
// in library linking.
float copysignf(float, float);

int main()
{
  float x;
  float y;
  float result = copysignf(x, y);
  __CPROVER_assert(
    __CPROVER_signf(result) == __CPROVER_signf(y), "signs match");
  return 0;
}
