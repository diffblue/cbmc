void (*f_ptr)(void);

int global;

void f1(void)
{
  global=1;
}

void f2(void)
{
  global=2;
}

int main()
{
  int input;

  f_ptr=f1;
  f_ptr();
  assert(global==1);
  
  f_ptr=f2;
  f_ptr();
  assert(global==2);

  f_ptr=input?f1:f2;
  f_ptr();
  assert(global==(input?1:2));
}
