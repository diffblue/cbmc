void dummy()
{
  // gcc eats this
  int i;
  extern int i;
}

int x = 5;

int f() {
  int x = 3;
  {
    extern int x;
    // this isn't the one above!
    return x;
  }
}
              
int main()
{
  int ret;

  ret=f();
  
  assert(ret==5);
}
