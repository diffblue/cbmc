int x;
int *p; // has value &x in the snapshot

int main()
{
  x = 1;

  assert(*p == 1);

  return 0;
}
