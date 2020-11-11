extern int g_in1;
extern int g_in2;

int g_out;

void func(void);

void main(void)
{
  g_in1 = 1;

  func();
}

void func(void)
{
  if(g_in1 == 0)
    g_out = 1; // unreachable.

  if(g_in2 == 0)
    g_out = 2;

  if(g_in1 == 0 && g_in2 == 0)
    g_out = 3; // unreachable, but not .
}
