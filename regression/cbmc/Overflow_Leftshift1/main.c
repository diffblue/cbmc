int main()
{
  unsigned char x;
  unsigned r=x << ((sizeof(unsigned)-1)*8);
  r=x << ((sizeof(unsigned)-1)*8-1);
  r=(unsigned)x << ((sizeof(unsigned)-1)*8);

  int s=-1 << ((sizeof(int)-1)*8);
  s=-256 << ((sizeof(int)-1)*8);
  return 0;
}
