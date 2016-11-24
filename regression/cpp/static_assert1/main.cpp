static_assert(1==1, "1==1");

static_assert(sizeof(int)==sizeof(int), "sizeof(int)==sizeof(int)");

class C1
{
  static_assert(2==2, "2==2");
  
  typedef int T;
  static_assert(sizeof(T)==sizeof(int), "sizeof(T)==sizeof(int)");
};

template<typename T>
class C2
{
  static_assert(sizeof(T)==sizeof(char), "sizeof(T)==sizeof(char)");
};

C2<char> C2_inst;

int main()
{
  typedef double T;
  static_assert(sizeof(T)==sizeof(double), "sizeof(T)==sizeof(double)");
}
