
typedef void (*fp_t)(int, int);

void add(int a, int b)
{
}
void subtract(int a, int b)
{
}
void multiply(int a, int b)
{
}

int main()
{
  // fun_ptr_arr is an array of function pointers
  void (*fun_ptr_arr[])(int, int) = {add, subtract, add};

  // Multiply should not be added into the value set
  fp_t other_fp = multiply;
  void (*fun_ptr_arr2[])(int, int) = {multiply, subtract, add};

  // the fp removal over-approximates and assumes this could be any pointer in the array
  (*fun_ptr_arr[0])(1, 1);

  return 0;
}
