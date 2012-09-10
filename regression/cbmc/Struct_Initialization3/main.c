typedef struct
{
 int a;
} S;
 
int main(void)
{
  S s;
  S *var1=&s;
  S var2 = *var1;
}
