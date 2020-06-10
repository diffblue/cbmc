\ingroup module_hidden 
\page nondet-volatile Modelling of Volatile Variables

This document describes the options available in goto-instrument for modelling
the behaviour of volatile variables. The following options are provided:

- `--nondet-volatile`
- `--nondet-volatile-variable <variable>`
- `--nondet-volatile-model <variable>:<model>`

By default, cbmc treats volatile variables the same as non-volatile variables.
That is, it assumes that a volatile variable does not change between subsequent
reads, unless it was written to by the program. With the above options,
goto-instrument can be instructed to instrument the given goto program such as
to (1) make reads from all volatile expressions non-deterministic
(`--nondet-volatile`), (2) make reads from specific variables non-deterministic
(`--nondet-volatile-variable`), or (3) model reads from specific variables by
given models (`--nondet-volatile-model`).

Below we give two usage examples for the options. Consider the following test,
for function `get_celsius()` and with harness `test_get_celsius()`:

```C
#include <assert.h>
#include <limits.h>
#include <stdint.h>

// hardware sensor for temperature in kelvin
extern volatile uint16_t temperature;

int get_celsius()
{
  if(temperature > (1000 + 273))
  {
    return INT_MIN; // value indicating error
  }
  
  return temperature - 273;
}

void test_get_celsius()
{
  int t = get_celsius();
  
  assert(t == INT_MIN || t <= 1000);
  assert(t == INT_MIN || t >= -273);
}
```

Here the variable `temperature` corresponds to a hardware sensor. It returns
the current temperature on each read. The `get_celsius()` function converts the
value in Kelvin to degrees Celsius, given the value is in the expected range.
However, it has a bug where it reads `temperature` a second time after the
check, which may yield a value for which the check would not succeed. Verifying
this program as is with cbmc would yield a verification success. We can use
goto-instrument to make reads from `temperature` non-deterministic:

```
goto-cc -o get_celsius_test.gb get_celsius_test.c
goto-instrument --nondet-volatile-variable temperature get_celsius_test.gb get_celsius_test-mod.gb
cbmc --function test_get_celsius get_celsius_test-mod.gb
```

Here the final invocation of cbmc correctly reports a verification failure.

However, simply treating volatile variables as non-deterministic may for some
use cases be too inaccurate. Consider the following test, for function
`get_message()` and with harness `test_get_message()`:

```C
#include <assert.h>
#include <stdint.h>

extern volatile uint32_t clock;

typedef struct message {
  uint32_t timestamp;
  void *data;
} message_t;

void *read_data();

message_t get_message()
{
  message_t msg;
  
  msg.timestamp = clock;
  msg.data = read_data();
  
  return msg;
}

void test_get_message()
{
  message_t msg1 = get_message();
  message_t msg2 = get_message();
  
  assert(msg1.timestamp <= msg2.timestamp);
}
```

The harness verifies that `get_message()` assigns non-decreasing timestamps to
the returned messages. However, simply treating `clock` as non-deterministic
would not allow to prove this property. Thus, we can supply a model for reads
from `clock`:

```C
// model for reads of the variable clock
uint32_t clock_read_model()
{
  static uint32_t clock_value = 0;
  
  uint32_t increment;
  __CPROVER_assume(increment <= 100);
  
  clock_value += increment;
  
  return clock_value;
}
```

The model is stateful in that it keeps the current clock value between
invocations in the variable `clock_value`. On each invocation, it increments
the clock by a non-determinstic value in the range 0 to 100. We can tell
goto-instrument to use the model `clock_read_model()` for reads from the
variable `clock` as follows:

```
goto-cc -o get_message_test.gb get_message_test.c
goto-instrument --nondet-volatile-model clock:clock_read_model get_message_test.gb get_message_test-mod.gb
cbmc --function get_message_test get_message_test-mod.gb
```

Now the final invocation of cbmc reports verification success.

