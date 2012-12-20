char a[100];

int main()
{
  char *p, *q;
  
  q=p;
  
  __CPROVER_assume(!__CPROVER_same_object(p, 0));
  
  p++;
  
  assert(!__CPROVER_same_object(p, 0));
}
