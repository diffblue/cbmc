int cpp_f(int fkt_argument)
{
}

extern "C" void f(int fkt_argument)
{
}

// order matters

extern "C" void g(int fkt_argument);

// same as above!
void g(int fkt_argument)
{
}

int main()
{
  cpp_f(0);
  f(0);
  g(0);
}
