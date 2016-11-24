namespace std
{
  struct A {int i; };
}

std::A a;

int main(int argc, char* argv[])
{
  assert(a.i == 0);
}
