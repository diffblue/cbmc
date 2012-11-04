extern "C" void f(char)
{
}

// different!
extern "C++" void f(int)
{
}

void g(int)
{
}

// different!
extern "C" void g(char)
{
}

int main()
{
  f(int(1));
  f(char(1));
  g(int(1));
  g(char(1));
}
