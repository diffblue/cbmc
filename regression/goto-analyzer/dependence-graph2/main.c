
int f(void);
extern int in;
int out;

void main(void)
{
  if (in)
    out = f();
}

