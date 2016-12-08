int intx;

int main()
{
  int i;

  // This should be converted into a bit-wise AND
  // (not an address-of).
  i=(intx)&i;

  // This is an address-of.
  i=(long int)&i;
}
