// This is a bug derived from:
//  /usr/include/c++/4.7/ext/type_traits.h
// Which is GPL V3

template<typename T, bool = false>
struct p
{ typedef double type; };

template<typename T>
struct p<T, false>
{ };

template<>
struct p<long double>
{ typedef long double type; };

int main()
{
}
