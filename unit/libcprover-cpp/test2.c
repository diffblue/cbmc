// Input file to test reading through API, not for compiling!
// Compared to test.c, this is supposed to have a passing assertion.

int main(int argc, char *argv[])
{
  int arr[] = {0, 1, 2, 3, 4};
  __CPROVER_assert(arr[3] == 3, "expected success: arr[3] to be 3");
}
