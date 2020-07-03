extern int ar[2];
extern int in;
int out1, out2, out3;

void array_task(void)
{
  if(in == 1)
    ar[0]++;

  if(in == 2)
    ar[1]++;

  out1 = ar[0];
  out2 = ar[1];
  out3 = ar[0] + ar[1];
}
