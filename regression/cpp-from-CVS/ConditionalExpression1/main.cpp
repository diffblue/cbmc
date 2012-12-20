int main()
{
     bool b;
     int a = 0;
     int c = 0;
     
     b ? a += 1 : c +=1;

    assert(a == 1 || a == 0);
    assert(c == 1 || c == 0);
    assert( a != c);
}
