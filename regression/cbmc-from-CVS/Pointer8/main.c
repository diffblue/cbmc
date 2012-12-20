#define NULL ((void *)0)

typedef struct pair {
	int first;
	int second;
} pair;

typedef struct map {
	struct map *next;
	pair p;
} map;

map data0;
map data1;

int main() {
  data0.next = &data1;
  data0.p.first = 1;
  data0.p.second = 2;

  data1.next = NULL;
  data1.p.first = 2;
  data1.p.second = 4;

  {
    map *ptr = data0.next;

    assert(ptr->p.first == 2);
    assert(ptr->p.second == 4);
  }

  return 0;
}
