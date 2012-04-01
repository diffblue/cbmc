int cpp_f(int fkt_argument)
{
}

extern "C" void f(int fkt_argument)
{
}

// order matters

extern "C" void g(int fkt_argument);

void g(int fkt_argument)
{
}

int main()
{
}
