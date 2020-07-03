struct st
{
  int a;
  int b;
};

struct st sts_inf;

void func(struct st *inf); // no body

void main(void)
{
  func(&sts_inf); // assertion failed here
}
