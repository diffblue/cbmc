void *malloc(__CPROVER_size_t);
void free(void *);

int main()
{
  int *p=malloc(sizeof(int));
  int x;
  int i, y;
  i=y;

  if(i==4711) p=&x;

  // should fail if i==4711
  free(p);
}
