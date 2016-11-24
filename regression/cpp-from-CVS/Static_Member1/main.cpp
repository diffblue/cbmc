class B
{
public:
  static int A1;
  static int A2;
  static const int A3=20;
  
  // the const ones are good as array size
  int table[A3];
};

int B::A1=1;
int B::A2;

int main()
{
  assert(B::A1==1);
  assert(B::A2==0); // zero initializer
  assert(B::A3==20); // in-class initializer
}
