unsigned strlen(const char *);

// my own version, which returns the length +1
unsigned strlen(const char *s)
{
  unsigned int result=1;
  while(*s!=0) { s++; result++; }
  return result;  
}

int main()
{
  assert(strlen("asd")==4);
}
