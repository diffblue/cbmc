typedef int (*function_ptr_t)(void);

struct simple_function_pointer_wrapper
{
  function_ptr_t function;
};

int call_struct_function_pointer(
  struct simple_function_pointer_wrapper *wrapper)
{
  return wrapper->function();
}

int call_array_function_pointer(function_ptr_t functions[])
{
  return functions[0];
}

struct complicated_function_pointer_wrapper
{
  function_ptr_t functions[3];
};

int call_complicated_function_pointer_wrapper(
  struct complicated_function_pointer_wrapper *wrapper)
{
  return wrapper->functions[0]();
}

int const_1(void)
{
  return 1;
}

int main(void)
{
  struct simple_function_pointer_wrapper simple_wrapper = {.function =
                                                             &const_1};
  assert(call_struct_function_pointer(&simple_wrapper));

  function_ptr_t functions[] = {const_1};
  assert(call_array_function_pointer(functions));

  struct complicated_function_pointer_wrapper complicated_wrapper = {
    .functions = {const_1, const_1}};
  assert(call_complicated_function_pointer_wrapper(&complicated_wrapper));
}
