int *nondet_ptr();

int main()
{
  int *ptr;
  ptr = nondet_ptr();
  if(ptr == 0)
    return;
  __CPROVER_assert(ptr != 0, "pointer cannot be null");
}
