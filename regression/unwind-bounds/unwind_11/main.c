
void func1()
{
  int i;

  for (i = 0; i < 4; i++) {} // func.0: 4
}

void func2()
{
  int i;

  // The current constant propagator works function-wise, hence we get a bound
  // for this loop even though it is not reachable from the entry point
  for (i = 0; i < 3; i++) {} // func2.0: 3
}

int main()
{
  func1();
}

