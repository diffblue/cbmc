int main()
{
  {
    unsigned i, j, k, l;
  
    j=k;
    i=j/2;
    l=j>>1;
    assert(i==l);

    j=k;
    i=j%2;
    l=j&1;
    assert(i==l);
  }
  
  {
    signed int i, j, k, l;

    // shifting rounds into the wrong direction
    __CPROVER_assume(!(k&1));
    j=k;
    i=j/2;
    l=j>>1;
    assert(i==l);

    j=k;
    i=j%2;
    l=j&1;
    assert(i==l);
    
  }
}
