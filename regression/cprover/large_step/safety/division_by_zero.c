int main()
{
  int x, y, z;

  z = 10 / x; // unsafe

  if(y != 0)
    z = 10 / y; // safe
}
