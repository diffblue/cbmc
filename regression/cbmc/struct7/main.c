struct my_struct
{
  int i;
  int array[10];
} s;

void f(int *p)
{
  int diff;
  
  diff=p-&s.array[0];

  // should pass
  *p=1;
}

int main()
{
  int ind, x;
  ind=x;
  int *p=&s.array[ind];
  
  if(ind>=0 && ind<=9)
    f(p);
}
