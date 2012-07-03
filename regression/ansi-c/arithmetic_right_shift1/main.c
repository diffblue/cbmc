#define static_assert(x) struct { char some[(x)?1:-1]; }

// arithmetic shift right isn't division!
// http://en.wikipedia.org/wiki/Arithmetic_shift 

static_assert((-70)/16==-4);
static_assert((-70)>>4==-5);
static_assert((-16)>>1==-8);
static_assert((-1)>>1==-1);
static_assert(70>>4==4);

int main()
{
}
