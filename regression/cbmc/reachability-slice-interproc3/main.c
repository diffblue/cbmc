void intermediate();
void root();

int main()
{
  intermediate();
  return 1;
}

void intermediate()
{
  root();
}

void root()
{
  __CPROVER_assert(0, "");
  intermediate();
}
