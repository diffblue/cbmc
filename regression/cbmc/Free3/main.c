void *malloc(__CPROVER_size_t size);
void free(void *p);

int main()
{
  int *p;
  unsigned int n;

  p=malloc(sizeof(int)*10);

  free(p);

  // well, a double-free
  free(p);
}
