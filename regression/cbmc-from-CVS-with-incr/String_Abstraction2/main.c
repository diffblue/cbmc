unsigned strlen(const char *);
char *strcpy(char *, const char *);

int main()
{
  char a[100], b[100], *p;
  unsigned int i;
  
  i=strlen("asdasd");
  
  strcpy(a, "asd");
  strcpy(b, "asd");
  
  p=i?a:b;
  
  i=strlen(p);
  
  assert(i==3);
}
