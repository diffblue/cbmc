int main()
{
  void *table[]={ &&l0, &&l1, &&l2 };
  int in, out;
  
  if(in>=0 && in<=2)
  {
    goto *(table[in]);

   l0: out=0; goto result;
 
   l1: out=1; goto result;
 
   l2: out=2; goto result;
   
   result:
     assert(in==out);
  }
}
