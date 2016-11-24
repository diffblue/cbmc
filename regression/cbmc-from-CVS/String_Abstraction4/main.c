unsigned strlen(const char *);
char *strcpy(char *dest, const char *src);

int main()
{
  char a[100], b[101];

  b[100]=0;

  // this should fail, off by one!
  strcpy(a, b);
}
