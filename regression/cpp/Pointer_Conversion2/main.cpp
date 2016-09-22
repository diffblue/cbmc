struct some_struct {int whatnot;};

int main()
{
  void *ptr1;
  int some_struct::* ptr2;
  int (*ptr3)(int);
  
  // The number '0' can be converted to any pointer
  ptr1=0;
  ptr2=0;
  ptr3=0;
}
