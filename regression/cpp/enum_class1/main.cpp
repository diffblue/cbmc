enum class Color1 : char { red, blue };

enum Color2 : char { red, blue };

// defaults to int
enum class TrafficLight { red, yellow, green };

static_assert(sizeof(Color1)==sizeof(char), "size of Color1");
static_assert(sizeof(Color2)==sizeof(char), "size of Color2");
static_assert(sizeof(Color1::red)==sizeof(char), "size of Color1::red");
static_assert(sizeof(TrafficLight::red)==sizeof(int), "size of TrafficLight::red");

int main()
{
  Color1 c;
  c=Color1::red;

  Color2 c2;
  c2 = red;
}
