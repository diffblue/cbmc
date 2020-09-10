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
  struct my_struct
  {
    fp_t first_pointer;
    fp_t second_pointer;
  } struct1;

  struct1.first_pointer = add;

  // Multiply and subtract should not be added into the value set
  fp_t other_fp = multiply;
  struct1.second_pointer = subtract;

  // this pointer can only be "add"
  struct1.first_pointer(1, 1);

  return 0;
}
