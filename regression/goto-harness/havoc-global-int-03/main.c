int x = 1;

int main()
{
  assert(x == 1); //unreachable, hence success
  assert(x == 2);
  assert(x == 3);

  return 0;
}
