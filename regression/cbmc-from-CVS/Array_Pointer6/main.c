typedef int a_type[100];

a_type array;

int *p;
a_type *q;

int main()
{
  p=array;
  q=&array;
  q++;
  q--;
  
  assert(**q==*p);
}
