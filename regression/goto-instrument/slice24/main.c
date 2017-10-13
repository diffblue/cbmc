#include <assert.h>
#include <malloc.h>

struct rrr
{
    char j;
    int y;
};

void foo(struct rrr *r)
{
    r->j = 1;
}

int main(int argc, char* argv[])
{
    struct rrr* r=malloc(sizeof(struct rrr));
    foo(r);
    if (r->j==1)
    {
        assert(1);
        return 0;
    }
    return -1;
}

