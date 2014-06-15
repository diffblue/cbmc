unsigned strlen(const char *);
char *strcpy(char *dest, const char *src);
const char *strerror(int);

int main(int argc, char *argv[])
{
  // this should work
  char *my_ptr=argv[0];

  // this should work
  int i=strlen(my_ptr);
}
