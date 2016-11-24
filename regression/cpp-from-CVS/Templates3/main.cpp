template<unsigned int size>
class int_array
{
public:
  int array[size];
  
  int read(unsigned int x)
  {
  	assert(x<size);
  	return array[x];
  }
};

int main()
{
  int_array<3> a;
  a.read(2);
}
