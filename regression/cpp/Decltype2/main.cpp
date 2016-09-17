// C++11
// decltype is a C++11 feature to get the "declared type" of an expression.
// It is similar to 'typeof' but handles reference types "properly".

class base {};
class derived : public base {};

derived d;

decltype(static_cast<derived *>(&d)) z;

int main()
{
}
