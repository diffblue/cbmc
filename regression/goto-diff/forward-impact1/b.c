int compute(int v)
{
  return v * 3;
}

int process(int v)
{
  return compute(v) + 1;
}

int main()
{
  return process(5);
}
