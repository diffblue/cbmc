int compute(int v)
{
  return v * 2;
}

int process(int v)
{
  return compute(v) + 1;
}

int main()
{
  return process(5);
}
