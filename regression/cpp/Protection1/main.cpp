class A
{
  int i;
  A(int i) : i(i)
  {
  }

private:
  A(); // disabled
};

class B : A
{
};

int main(int argc, char *argv[])
{
  B b;
}
