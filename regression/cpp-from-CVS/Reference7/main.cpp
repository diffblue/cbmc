
int main()
{
 int i = 8;
 int* p = &i;
 int*& rp = p;
 assert(*rp == 8);
}
