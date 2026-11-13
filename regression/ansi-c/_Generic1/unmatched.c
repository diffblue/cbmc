int main(void)
{
  int arr[2];
  // the diagnostic reports the lvalue-converted controlling type
  return _Generic(arr, int: 1);
}
