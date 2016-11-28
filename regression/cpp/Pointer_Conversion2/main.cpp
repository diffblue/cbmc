struct some_struct {int whatnot;};

int main()
{
  void *ptr1;
  int some_struct::* ptr2; // this is a member pointer
  int (some_struct::*ptr3)(int); // this is a pointer to a method
  int (*ptr4)(int); // function pointer

  // The number '0' can be converted to any pointer
  ptr1=0;
  ptr2=0;
  ptr3=0;
  ptr4=0;
}
