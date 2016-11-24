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

// same again inside a namespace
namespace SOME
{
  extern "C" void somef(char)
  {
  }
  
  extern "C++" void somef(int)
  {
  }
}

using SOME::somef;

int main()
{
  f(int(1));
  f(char(1));
  g(int(1));
  g(char(1));
  somef(int(1));
  somef(char(1));
}
