// these are constants!

int const C1=10;
enum { C2=20 };

const int C3=1;

class my_class
{
public:
  static const int C4=1;
};

// this checks that these are indeed constants
int array1[C1];
int array2[C2];
int array3[C3];
int array4[my_class::C4];

int main()
{
}
