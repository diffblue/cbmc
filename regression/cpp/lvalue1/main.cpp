enum asd { ASD };

int main()
{
  asd a, b;

  // casts to references are lvalues
  asd &c=(asd &)((int &)a |= (int &)b);
  
  // in C++, comma expressions are lvalues
  (a, b)=ASD;
}
