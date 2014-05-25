void *malloc(__CPROVER_size_t);
void free(void *);

int main()
{
  int *p=malloc(sizeof(int));
  int *q=p;
  int i, x;
  i=x;
  
  if(i==4711) free(q);

  // should fail if i==4711
  *p=1;
}
