const char s[]="abc";

const char *my_array[]=
{
  "xyz",
  0
};

int main()
{
  const char *p1;
  p1=s;

  // this is a non-constant pointer
  // to a constant pointer to pointers to constant-chars
  const char * const *p2;
  p2=my_array;
  
  const char *p3;
  char ch;
  
  p3=*p2;
  
  ch=*p3;
  
  assert(ch=='x');
}
