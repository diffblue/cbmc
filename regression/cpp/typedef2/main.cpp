typedef unsigned *something, *TP;

void func(unsigned *)
{
}

void func2(TP tp)
{
  func(tp);
}

int main()
{
}
