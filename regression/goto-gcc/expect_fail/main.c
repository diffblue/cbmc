int foo(); // this is not defined and should cause linker errors

int main()
{
  return foo();
}
