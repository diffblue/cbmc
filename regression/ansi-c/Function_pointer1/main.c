float some_function(float a, float b)
{
  return 1.0;
}

float (*return_a_function_pointer(char a, char b))(float, float)
{
  return some_function;
}

typedef float(code_type)(float, float);

code_type * return_another_function_pointer(char a, char b)
{
  return some_function;
}

int main()
{
  return 0;
}
