
int main()
{
  int x, y;

  struct Ptr_struct
  {
    int* a;
    int* b;
  } ptr_struct;

  ptr_struct.a=&x;
  ptr_struct.b=&y;

  // value set must not be ptr_struct.a==&y

  return 0;

}
