int main()
{
  int x = 5;
  int y;
  int z = 8;

  // Negative case
  __CPROVER_assert(x / y != 0, "This assertion is falsifiable");

  // Positive case
  __CPROVER_assert(
    x / z != 0, "This assertion is valid under all interpretations");

  return 0;
}
