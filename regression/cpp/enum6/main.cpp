
enum TAG { E1, E2, E3 } a;

struct Z
{
public:
  enum TAG field1 : 3;
  enum TAG field2 : 4;
  enum TAG field3 : 1;
} z;

int main()
{
  a=z.field1;
  z.field1=a;
  z.field1=z.field3;
}
