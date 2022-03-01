void *malloc(__CPROVER_size_t);
void *realloc(void *, __CPROVER_size_t);

int main()
{
  int *p = malloc(sizeof(int));
  p++;
  int *q = realloc(p, sizeof(int) * 2); // fails, offset not zero
}
