static const int my_ids[] = { 1, 2, 3, 4 };

#ifdef __GNUC__
extern typeof(my_ids) my_ids_table __attribute__((alias("my_ids")));
#endif

int main()
{
}
