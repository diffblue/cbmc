_Bool nondet_bool();

void foo()
{
  unsigned i = 0;
head:
  i++;
  if(nondet_bool())
    goto head;
  if(i < 5)
    goto head;
}

int main()
{
  foo();
  return 0;
}
