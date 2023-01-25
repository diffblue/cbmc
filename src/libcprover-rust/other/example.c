// File just to allow smoke testing of Rust API while tests are run.

int main(int argc, char *argv[])
{
  int arr[] = {0, 1, 2, 3};
  __CPROVER_assert(arr[3] != 3, "expected failure: arr[3] == 3");
}
