int global;

int main()
{
  global=1;

  __CPROVER_ASYNC_1: assert(global==1);

  __CPROVER_ATOMIC_BEGIN();
  global=2;
  // no interleaving here
  global=1;
  __CPROVER_ATOMIC_END();
}
