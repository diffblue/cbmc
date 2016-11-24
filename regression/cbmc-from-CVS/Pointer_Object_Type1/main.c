int int_var;
char ch_var;

int main()
 {
  int input;
  void *p;
  int *p2;
  
  if(input)
    p=&int_var;
  else
    p=&ch_var;
    
  p2=(int *)p;

  // this should fail if p points to ch_var
  (*p2)++;
 }
