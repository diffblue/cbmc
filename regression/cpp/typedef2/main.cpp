typedef unsigned int T;

typedef T *something, *TP;

void func(unsigned int *)
{
}

void func2(TP tp)
{
  func(tp);
}

int main()
{
}

