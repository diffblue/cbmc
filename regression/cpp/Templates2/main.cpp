template <int size>
class int_array
{
public:
  int array[size];
};

int main()
{
  int_array<3> a;
  a.array[0]=1;
}
