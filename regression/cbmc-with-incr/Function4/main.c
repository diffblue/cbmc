int nondet_int();

int f1()
{
  int ret;
  return ret;
}

typedef struct {
  int x;
} Str1;

int main()
{
  Str1 st;
  int x;

  st.x = nondet_int();  // comment this line - and everything is OK
  st.x = f1();
  x = nondet_int();
  st.x = x;
  
  return 0;
}
