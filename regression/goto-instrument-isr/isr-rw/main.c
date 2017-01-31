int global=0;

void isrA()
{
  global=1;
}

int main()
{
  int x=global;
  assert(x==0);
}
