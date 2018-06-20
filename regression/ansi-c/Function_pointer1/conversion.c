int (*ptr2)[2];
int (*ptrX)[];

int main()
{
  ptrX=ptr2;
  ptr2=ptrX;
}
