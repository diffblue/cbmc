
union union_tag_name
{
	int x;
	float y;
};

int main()
{
  const union union_tag_name my_union_var = {.y = 3.15};
  const double z = 4;
  return 0;
}
