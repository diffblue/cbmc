unsigned strlen(const char *);
char *strcpy(char *dest, const char *src);

int main()
{
  char a[100], b[100], *p;

  strcpy(a, "asdasd\000");
  assert(strlen(a+1)==5);
  
  p=a+1;
  assert(strlen(p)==5);

  a[10]=0;
  assert(strlen(a)==6);

  a[3]=0;
  assert(strlen(a)==3);
}
