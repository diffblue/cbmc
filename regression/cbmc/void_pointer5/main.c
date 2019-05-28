int main(int argc, char *argv[])
{
  void *p;
  if(argc > 0)
    p = argv[0];
  char A[1];
  __CPROVER_array_copy(A, p + 1);
  __CPROVER_assert(0, "");
}
