void *malloc(__CPROVER_size_t);
void free(void *);

int main()
{
  int *p = malloc(sizeof(int));
  p++;
  free(p); // fails, offset is not zero
}
