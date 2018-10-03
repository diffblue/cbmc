#if TEST == 0
const struct buffer *foo();

typedef struct buffer
{
  int head;
} buffer_t;
#endif

#if TEST == 1
struct buffer *foo();

typedef struct buffer
{
  int head;
} buffer_t;
#endif

#if TEST == 2
typedef struct buffer
{
  int head;
} buffer_t;

const struct buffer *foo();
#endif

static void clear(buffer_t *buf)
{
  buf->head = 0u;
}

int main()
{
  return 0;
}
