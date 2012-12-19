enum enumname { ASD, ASD2 };

// enum tags have a separate namespace
typedef enum enumname enumname;

int main()
{
  enumname x;
  
  x=ASD;
}
