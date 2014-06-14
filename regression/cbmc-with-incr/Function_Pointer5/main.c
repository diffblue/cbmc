// this is a pointer to a function that takes a function pointer as argument

void signal1(int, void (*)(int));
void signal2(int, void (*h)(int));

void handler(int x)
{
}

int main()
{
  signal1(1, handler);
  signal2(2, handler);
}
