int g_in1, g_in2;
int g_out;

void main(void)
{
  int t;
  if(g_in1)
  {
    if(g_in2)
      t = 0;
    else
      t = 1;

    g_out = 1; // depends on "if(g_in1)
  }
}
