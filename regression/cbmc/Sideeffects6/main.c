int main()
{
  int c, x, y, z;

  // we should be able to find this division by zero
  (void)(c?x/y:z);
  
  return 0;
}
