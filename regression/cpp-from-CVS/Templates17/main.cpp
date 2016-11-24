
template <class T>
struct A
{
	bool b;
	A(){}
};

template <>
struct A<bool>;

template <>
struct A<bool>{bool b;};


int main()
{
	A<bool> a;
	a.b = false;
}
