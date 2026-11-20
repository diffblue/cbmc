int true_from_calling_context = 0;

int example_function(int argument)
{
  int local = argument + 1;
  int location = 1;

  for(int i = 0; i < 10; ++i)
  {
    location = 2;
    ++local;
  }

  location = 3;
  ++local;

  return location + local;
}

int main(int argc, char **argv)
{
  true_from_calling_context = 1;

  int argument_input = 1;

  int ret = example_function(argument_input);

  return 0;
}
