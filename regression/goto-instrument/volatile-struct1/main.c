
struct struct_tag_name
{
	int x;
	float y;
};

int main()
{
  volatile struct struct_tag_name my_struct_var = {.x =  1, .y = 3.15};
  const double z = 4;
  return 0;
}
