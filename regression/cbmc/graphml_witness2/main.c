extern void __VERIFIER_error();

static float one(float *foo)
{
  return *foo;
}

static float two(float *foo)
{
  return *foo;
}

float x = 0;

void step()
{
  x = one(0);
}

int main(void)
{
  while(1)
  {
    step();
    if(x == 0)
    {
      __VERIFIER_error();
    }
  }
  return 0;
}
