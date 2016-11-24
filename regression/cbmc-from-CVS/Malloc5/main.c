_Bool nondet_bool();
void *malloc(unsigned s);

int analyze_this()
{
  char *p_char=malloc(sizeof(char));
  int *p_int=malloc(sizeof(int));
  void *p;
  
  p=nondet_bool()?p_char:p_int;

  p_int=p;
  
  // this should fail, as a char is too small
  *p_int=1;
}

int main()
{
  analyze_this();
}
