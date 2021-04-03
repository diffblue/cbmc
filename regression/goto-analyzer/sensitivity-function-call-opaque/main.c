int global_value;

int opaque(int other, int *side_effect);

int main()
{
  int x = 3;
  int y = 4;

  global_value = 4;

  int z = bar(x + 1, &y);

  __CPROVER_assert(x == 3, "assertion x == 3"); // Success
  __CPROVER_assert(
    y == 4,
    "assertion y == 4"); // Unknown - the opaque function could have modified it
  __CPROVER_assert(
    z == 0,
    "assertion z == 0"); // Unknown - the opaque function could have returned anything
  __CPROVER_assert(
    global_value == 4,
    "assertion global_value == 4"); // Unknown - the opaque function could have modified this

  return 0;
}
