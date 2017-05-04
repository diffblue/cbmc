int global=0;

void isrA()
{
  int a=global;
  assert(0); // unreachable
}

int main()
{
  int x=global;
}
