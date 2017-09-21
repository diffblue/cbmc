int g = 0;

int main(void)
{
    assert(g == 0);
    g = (g == 0) ? 1 : 0;
}
