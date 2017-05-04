int global=0;

void isrA()
{
  int a=global;
  assert(a==0);
}

int main()
{
  global=1;
}
