int main()
{
   int s=0;
   int t=0;
   t=(s=3,s+2);
   assert(s==3);
   assert(t==5);
}
