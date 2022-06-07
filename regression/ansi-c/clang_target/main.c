int main()
{
  int A[sizeof(void *) == 4 ? 1 : -1];
}
