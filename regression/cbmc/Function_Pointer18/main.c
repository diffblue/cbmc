void (*my_ptr)();

void my_f()
{
  asm("mfence");
  my_ptr=my_f;
}

int main()
{
  void (*nondet)();
  nondet();
}
