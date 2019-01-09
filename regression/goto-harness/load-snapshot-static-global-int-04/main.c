int x;

int main()
{
  x = 0; // should be skipped

  assert(x == 1);

  return 0;
}
