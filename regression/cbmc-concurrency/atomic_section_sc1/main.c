int global;

int main()
{
  __CPROVER_ASYNC_1: global=2;

  __CPROVER_ATOMIC_BEGIN();
  global=1;
  // no interleaving here
  assert(global==1);
  __CPROVER_ATOMIC_END();
}
