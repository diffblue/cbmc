const int ASD1=1;

int array[ASD1];

int main()
{
  // this sound fail!
  (int &)ASD1=2;
}
