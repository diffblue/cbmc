template <class T>
class A
{
	T t;
};

int main()
{
	A<A<double> > a1;
	A<A<int> > a2;
}
