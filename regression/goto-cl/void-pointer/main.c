void *malloc(__CPROVER_size_t);
int printf(const char *, ...);

int main(int argc, char *argv[])
{
  void *p = malloc(2);
  printf("%p\n", p);
#ifdef VOID1
  (void)*p;
#else
  void *q = &p[1];
  printf("%p\n", q);
#endif
  return 0;
}
