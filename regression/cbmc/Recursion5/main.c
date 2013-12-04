void loop();

void rec()
{
  loop();
}

void loop()
{
  while(nondet_bool())
    rec();
}

int main()
{
  rec();

  __CPROVER_assert(0, "");

  return 0;
}

