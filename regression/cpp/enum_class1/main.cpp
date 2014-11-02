enum class Color : char { red, blue };

// defaults to int
enum class TrafficLight { red, yellow, green };

static_assert(sizeof(Color)==sizeof(char), "size of Color");
static_assert(sizeof(Color::red)==sizeof(char), "size of Color::red");
static_assert(sizeof(TrafficLight::red)==sizeof(int), "size of TrafficLight::red");

int main()
{
  Color c;
  c=Color::red;
}
