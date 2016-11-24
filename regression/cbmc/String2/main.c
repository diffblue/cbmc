char *p="abc";

int main()
{
  int input;
  char ch;

  /* should result in bounds violation */  
  ch=p[input];
}
