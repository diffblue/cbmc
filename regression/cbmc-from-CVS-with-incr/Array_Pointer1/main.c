int a[4];
int *p;

int main()
{
  int j;

  a[1] = 100;

  p = a;
  p++;
  *p = 1; // sets a[1]

  j = a[1];

  assert(j == 1);
  
  // Assignment with (dummy) cast.
  // The array should be zero-initialized.
  p=(int *)a;
  assert(*p==0);
}
