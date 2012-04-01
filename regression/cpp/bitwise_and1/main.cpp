int intx;

int main()
{
  int i;

  // this should be converted into a bit-wise AND
  // (not an address-of)

  i=(intx)&i;
}
