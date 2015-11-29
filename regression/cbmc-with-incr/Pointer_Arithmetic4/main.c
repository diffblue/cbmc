int a[]={ 10, 20, 30 };
int *p, z;

int main()
{
  p=a-1;
  z=p[2];
  assert(z==20);
}
