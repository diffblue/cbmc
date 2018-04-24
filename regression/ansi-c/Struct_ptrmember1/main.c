struct some_struct
{
  int some_field;
} array[10];

int main()
{
  array[0].some_field=1;
  array->some_field=1;
}
