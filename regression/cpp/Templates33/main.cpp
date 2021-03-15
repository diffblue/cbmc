template<typename T>
class X
{
public:
  typename T::asd asd;
};

// this won't fail!
typedef X<char> Z;

int main()
{
}
