int main()
{
  int x, *p;
  p = &x;
  *p; // ok
  p++;
  *p; // not ok, out of bounds
  return 0;
}
