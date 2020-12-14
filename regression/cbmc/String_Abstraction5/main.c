__CPROVER_size_t strlen(const char *);
char *strcpy(char *dest, const char *src);
const char *strerror(int);

int main()
{
  char a[100];
  const char *p;
  __CPROVER_size_t i;

  // this should work
  p = strerror(1);

  // this should work
  i = strlen(p);

  // this should work
  if(i < sizeof(a))
    strcpy(a, p);

  // and even this should work
  char ch;
  ch = *p;
}
