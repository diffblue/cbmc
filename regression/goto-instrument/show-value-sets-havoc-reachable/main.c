int x;
int y;
int *p = &x;
int *q;

int main()
{
  int *local_p = &y;
#ifdef __GNUC__
  // an instruction that CBMC does not model
  asm volatile("unmodeled_instruction" ::: "memory");
#else
  __asm { unmodeled_instruction }
#endif
  int *r = q;
  return 0;
}
