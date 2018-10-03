int main(void)
{
  float f = 0.5;
  float g;

  float result = f + g;
  __CPROVER_assert(result >= 1.5, "");
}
