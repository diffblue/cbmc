int global;

void isrA()
{
  global=1;
}

int main()
{
  global=0;
  assert(global==0);
}
