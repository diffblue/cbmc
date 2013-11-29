unsigned my_strlen(const char *s)
{
  // this tests automatic unwinding
  unsigned x=0;
  while(*s) { s++; x++; }
  return x;
}

int main()
{
 int l;

 l=my_strlen("abcXYZ");

 assert(l==6);
}

