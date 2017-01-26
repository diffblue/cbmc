
int x;

int main()
{
  int i;

  for (i = 0; i < 3; i += 2) {} // main.0: 2

  // Currently not handled by the constant propagator
  for (i = 0; i < 4; i *= 2) {} // main.0: 2
}

