// clang-format off
int main(int argc, char **argv)
{
    int y;

    __CPROVER_assert(
        y != 0 ==> 10 / y <= 10,
        "10 / y is expected to succeed");
}
// clang-format on
