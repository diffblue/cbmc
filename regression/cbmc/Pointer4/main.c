_Bool nondet_bool();

int main()
{
  int *p=0;
  int x;

  if(nondet_bool())
    p=&x;

  if(p) *p=1;
}
