template <class T>
struct A;

template <class T>
struct A
{
	A(){}
};



template <>
struct A<bool>
{
	int b;
	A(){}
};


int main()
{
	A<bool> a;
	a.b = false;
}
