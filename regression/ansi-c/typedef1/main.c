typedef int INTTYPE;

INTTYPE my_int;

// this should work
void my_func1(int INTTYPE)
{
  INTTYPE++;
}

// even this should work!
void my_func2(INTTYPE INTTYPE)
{
  INTTYPE++;
}

int main()
{
}
