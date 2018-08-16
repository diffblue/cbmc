void func()
{
  asm("mfence");
}

int main(void)
{
  func();
}
