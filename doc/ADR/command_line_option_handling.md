\page command-line-option-handling Command-Line Option Handling Best Practices

**Date**: 27 Nov 2025
**Updated**: 27 Nov 2025
**Author**: Michael Tautschnig
**Domain**: Architecture, API, Developer Guidelines
**Description**: This document outlines best practices for adding and handling
    command-line options in CBMC and related tools. It explains the philosophy
    behind option design, the role of key data structures, and provides a
    step-by-step guide for implementing new options.
**Related Issue**: [#1521](https://github.com/diffblue/cbmc/issues/1521)

## Philosophy: Minimize Options, Maximize Usability

The guiding principle for command-line options in CBMC is: **minimize the
number of options exposed to users while providing sensible defaults**. This
philosophy serves several important goals:

### Why Minimize Options?

1. **Reduce Configuration Complexity**: Each new option adds to the cognitive
   load for users trying to understand the tool. Too many options can make the
   tool intimidating and difficult to learn.

2. **Prevent Configuration Errors**: More options means more ways for users to
   misconfigure the tool, potentially leading to incorrect results or poor
   performance.

3. **Maintain Consistency**: With fewer options, it's easier to ensure
   consistent behavior across different use cases and to reason about tool
   behavior.

4. **Simplify Testing**: The test space grows exponentially with each new
   option. Fewer options means more thorough testing is feasible.

### Providing Good Defaults

Instead of requiring users to configure every aspect of the tool's behavior,
strive to:

- **Choose sensible defaults** that work well for the majority of use cases
- **Auto-detect settings** when possible (e.g., platform characteristics)
- **Infer intent** from other options or the input program when appropriate
- **Fail safely** by enabling checks by default rather than disabling them

### When to Add a New Option

Before adding a new command-line option, consider these questions:

1. **Is this truly necessary?** Can the desired behavior be achieved through
   existing options or by improving defaults?

2. **Is the use case common enough?** Options for niche use cases should be
   avoided or kept undocumented (see below).

3. **Can this be auto-detected?** Many settings (like platform configurations)
   should be determined automatically rather than requiring user specification.

4. **Does this belong in the API instead?** Some configurations are better
   suited to programmatic API calls rather than command-line options.

## Policy on Undocumented Options

CBMC tools support **undocumented command-line options** for experimental
features and limited-use scenarios. This policy allows for:

### When to Use Undocumented Options

- **Debugging/Development Tools**: Options used primarily by CBMC developers
  for debugging or profiling (e.g., `--no-propagation`) don't need to be in the
  main help text.

- **Deprecated Features**: Options being phased out should remain functional
  but undocumented to avoid encouraging their use.

### Making Options "Undocumented"

To keep an option undocumented:

1. **Add it to the option macro** in the `*_parse_options.h` file (e.g.,
   `CBMC_OPTIONS`) so it's recognized by the parser.

2. **Implement its behavior** in the `doit()` or related methods.

3. **Omit it from the help text** in the `help()` method implementation.

Undocumented options can be discovered by examining the source code or through
word-of-mouth among power users, but won't appear in `--help` output.

## Key Data Structures

CBMC's command-line handling architecture separates concerns through three main
data structures. Understanding their roles is crucial for correctly implementing
option handling.

### The `cmdlinet` Object

**Purpose**: Raw, unfiltered command-line parsing

**Ownership**: Owned by `parse_options_baset` and its children (e.g.,
`cbmc_parse_optionst`, `goto_instrument_parse_optionst`)

**Characteristics**:
- Contains the raw results of parsing command-line arguments
- No validation or interpretation of values
- Available throughout the lifetime of the `*_parse_options` object
- Accessed via methods like `cmdline.isset("option-name")` and
  `cmdline.get_value("option-name")`

**Usage Pattern**:
```cpp
// In cbmc_parse_optionst::doit() or similar
if(cmdline.isset("my-option"))
{
  // Option was present on command line
  std::string value = cmdline.get_value("my-option");
  // Process the raw value...
}
```

**Key Point**: The `cmdlinet` object is the source of truth for what the user
actually typed on the command line, but it should not be passed deep into the
codebase.

### The `optionst` Structure

**Purpose**: Validated, processed configuration with defaults applied

**Ownership**: Created and populated by `*_parse_options` classes, then passed
as a `const` reference to other components

**Characteristics**:
- Stores processed and validated option values
- Includes defaults for options not specified on the command line
- Immutable after construction (passed as `const optionst &`)
- Provides type-safe accessors:
  - `get_option(name)` - returns string value
  - `get_bool_option(name)` - returns Boolean value
  - `get_signed_int_option(name)` - returns signed integer
  - `get_unsigned_int_option(name)` - returns unsigned integer
  - `get_list_option(name)` - returns list of strings
  - `is_set(name)` - checks if option was set

**Usage Pattern**:
```cpp
// Setting options (in parse_options)
optionst options;
if(cmdline.isset("my-flag"))
  options.set_option("my-flag", true);
else
  options.set_option("my-flag", false); // default

// Using options (in other components)
void some_function(const optionst &options)
{
  if(options.get_bool_option("my-flag"))
  {
    // Use the flag value
  }
}
```

**Key Point**: The `optionst` structure is the primary way configuration is
passed through the codebase. By passing it as `const`, we ensure that
configuration is determined once at startup and doesn't change during
execution.

### The `configt` Structure

**Purpose**: Global language and platform configuration

**Ownership**: Global singleton accessed via `config` variable

**Characteristics**:
- Stores language-specific settings (C standard, C++ standard, etc.)
- Stores platform settings (architecture, OS, word size, endianness)
- Can be auto-detected from the system or the goto-program being analyzed
- Typically set early in program execution
- Set via `config.set(cmdline)` which processes specific command-line options

**Usage Pattern**:
```cpp
// Setting configuration (in parse_options)
if(config.set(cmdline))
{
  // Error parsing config options
  usage_error();
  exit(CPROVER_EXIT_USAGE_ERROR);
}

// Later, configuration may be loaded from goto-program:
config.set_from_symbol_table(goto_model.symbol_table);

// Accessing configuration (anywhere)
if(config.ansi_c.mode == configt::ansi_ct::flavourt::FLAVOUR_GCC)
{
  // Handle GCC-specific behavior
}
```

**Key Point**: The `configt` structure should be used for settings that define
the "world" in which analysis happens (language semantics, platform
characteristics), while `optionst` should be used for tool behavior settings.

## Adding a New Command-Line Option: Step-by-Step Guide

This section provides a detailed walkthrough of how to add a new command-line
option to a CBMC tool. We'll use examples from `cbmc` but the pattern applies
to all tools.

### Step 1: Determine Necessity and Scope

Before writing any code, answer:

1. **Is this option really needed?** Review the philosophy section above.

2. **Which tools need this option?**
   - Single tool only? Add to that tool's options.
   - Multiple tools? Consider creating a shared macro.

3. **Should this be documented?** Review the policy on undocumented options.

4. **What type of option is it?**
   - Boolean flag (presence = true)
   - Option with value (e.g., `--option=value`)
   - Option with list of values
   - Language/platform configuration (use `configt`)

### Step 2: Add to BINARY_OPTIONS Macro

Edit `src/BINARY/BINARY_parse_options.h` (e.g., `src/cbmc/cbmc_parse_options.h`):

**For a tool-specific option:**
```cpp
// clang-format off
#define CBMC_OPTIONS \
  OPT_BMC \
  "(no-standard-checks)" \
  "(my-new-option)" \
  "(my-valued-option):" \
  OPT_FUNCTIONS
// clang-format on
```

Here `(my-new-option)` has no trailing colon, so it is a Boolean flag, whereas
`(my-valued-option):` has a trailing colon, so it requires a value. Real
definitions chain in many more entries -- both bare string literals and shared
`OPT_*` macros; see `src/cbmc/cbmc_parse_options.h` for a complete example.

Keep the `// clang-format off` / `// clang-format on` guard around the
definition: it is load-bearing, as clang-format otherwise reflows the
concatenated string literals and breaks the one-entry-per-line layout. The
option string is plain string-literal concatenation and cannot carry `//`
comments (a `//` before a `\` line continuation would comment out the
backslash), so keep any explanatory notes in the surrounding prose rather than
inside the macro.

**For an option shared across multiple tools:**

If the option is useful for multiple tools (like `--bounds-check` which applies
to cbmc, goto-instrument, goto-analyzer, etc.), create or extend a shared macro
instead:

1. Identify or create an appropriate shared macro (e.g., in
   `src/ansi-c/goto-conversion/goto_check_c.h` for check-related options)

2. Add your option to that macro:
```cpp
// clang-format off
#define OPT_GOTO_CHECK \
  "(bounds-check)(pointer-check)(memory-leak-check)" \
  "(my-new-check)" \
  "(div-by-zero-check)"
// clang-format on
```

3. Reference the shared macro in each tool's OPTIONS macro:
```cpp
// clang-format off
#define CBMC_OPTIONS \
  OPT_BMC \
  OPT_GOTO_CHECK
// clang-format on
```

**Important Notes**:
- Options without colons are Boolean flags (presence means true)
- Options with colons (`:`) require a value (e.g., `--option=value` or
  `--option value`)
- There is no optional-value (`::`) form; an option either takes a value (`:`)
  or it does not
- Use hyphens, not underscores, in option names (e.g., `my-option` not
  `my_option`)

### Step 3: Add to Help Text

If the option should be documented, add it to the help text in
`src/BINARY/BINARY_parse_options.cpp` (e.g., `src/cbmc/cbmc_parse_options.cpp`):

**For a tool-specific option**, add to the `help()` method:
```cpp
void cbmc_parse_optionst::help()
{
  std::cout << '\n' << banner_string("CBMC", CBMC_VERSION) << '\n'
    // ... other help sections ...
    << "\n"
    "Analysis options:\n"
    " --bounds-check               enable array bounds checks\n"
    " --my-new-option              description of what this does\n"
    " --my-valued-option <value>   description with value explanation\n"
    // ... more options ...
}
```

**For a shared option**, add to the shared help macro:

Edit the shared header file (e.g., `src/ansi-c/goto-conversion/goto_check_c.h`):

```cpp
#define HELP_GOTO_CHECK \
  " {y--bounds-check} \t enable array bounds checks\n"                         \
  " {y--my-new-check} \t description of the new check\n"                      \
  " {y--div-by-zero-check} \t enable division by zero checks\n"
```

Then include this help macro in each tool's help method:
```cpp
void cbmc_parse_optionst::help()
{
  std::cout << '\n' << banner_string("CBMC", CBMC_VERSION) << '\n'
    // ... other help sections ...
    HELP_GOTO_CHECK
    // ... more help sections ...
}
```

**Help Text Guidelines**:
- Use `{y--option}` for yellow-colored option names in help macros
- Use `\t` for alignment between option name and description
- Keep descriptions concise but informative
- Indicate if an option takes a value: `--option <value>` or `--option=<value>`
- Group related options together
- Mention defaults when they exist

### Step 4: Handle Language/Platform Options

If your option affects language or platform configuration (C standard, target
architecture, etc.), it should be handled by `configt`:

**No additional code needed** - `config.set(cmdline)` in the `doit()` method
automatically processes these options:

```cpp
int cbmc_parse_optionst::doit()
{
  // Early in doit()
  if(config.set(cmdline))
  {
    usage_error();
    return CPROVER_EXIT_USAGE_ERROR;
  }
  // ... continue ...
}
```

Just ensure your option is in the appropriate `OPT_CONFIG_*` macro in
`src/util/config.h`:

```cpp
// For C/C++ language options:
#define OPT_CONFIG_C_CPP                                                       \
  "D:I:(include)(function)"                                                    \
  "(c89)(c99)(c11)(c17)(c23)(cpp98)(cpp03)(cpp11)"                             \
  "(my-language-option)"        // Add here if language-related

// For platform options:
#define OPT_CONFIG_PLATFORM                                                    \
  "(arch):(os):"                                                               \
  "(my-platform-option):"       // Add here if platform-related
```

### Step 5: Parse and Set optionst Values

In `src/BINARY/BINARY_parse_options.cpp`, add code to parse the option from
`cmdline` and set it in `optionst`:

**Location**: Usually in a method like `get_command_line_options()` or directly
in `doit()`:

```cpp
void cbmc_parse_optionst::get_command_line_options(optionst &options)
{
  // ... existing option parsing ...
  
  // For a Boolean flag:
  if(cmdline.isset("my-new-option"))
    options.set_option("my-new-option", true);
  else
    options.set_option("my-new-option", false); // explicit default
  
  // For an option with a value:
  if(cmdline.isset("my-valued-option"))
  {
    std::string value = cmdline.get_value("my-valued-option");
    // Validate the value if necessary
    if(value.empty())
    {
      log.error() << "--my-valued-option requires a non-empty value"
                  << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option("my-valued-option", value);
  }
  // If not set, either set a default or leave unset
  else
  {
    options.set_option("my-valued-option", "default-value");
  }
  
  // For an integer option:
  if(cmdline.isset("my-numeric-option"))
  {
    options.set_option(
      "my-numeric-option",
      cmdline.get_unsigned_int_option("my-numeric-option"));
  }
  else
  {
    options.set_option("my-numeric-option", 10u); // default value
  }
  
  // ... more option parsing ...
}
```

**Important Guidelines**:

1. **Always set a default value** (even if it's false or empty string) to
   ensure `optionst` has a consistent state.

2. **Validate early**: Check for invalid values or conflicting options in
   `get_command_line_options()` or `doit()`, not deep in the codebase.

3. **Provide helpful error messages**: When validation fails, tell the user
   exactly what's wrong.

4. **Handle option conflicts**: If your option conflicts with others, detect
   and report it:
   ```cpp
   if(cmdline.isset("my-option") && cmdline.isset("conflicting-option"))
   {
     log.error() << "--my-option and --conflicting-option are mutually exclusive"
                 << messaget::eom;
     exit(CPROVER_EXIT_USAGE_ERROR);
   }
   ```

### Step 6: Use the Option in Implementation

Pass `optionst` as a `const` reference to the functions that need it:

```cpp
// Function signature
void my_analysis_function(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &message)
{
  if(options.get_bool_option("my-new-option"))
  {
    // Execute behavior enabled by the option
    message.status() << "my-new-option is enabled" << messaget::eom;
  }
  
  std::string value = options.get_option("my-valued-option");
  // Use the value...
}
```

**Never pass `cmdline` deep into the codebase.** The `cmdlinet` object should
only be used in `*_parse_options` classes. Once options are processed into
`optionst`, use that instead.

### Step 7: Avoid Threading Arguments Through Interfaces

One of the goals of using `optionst` is to avoid "threading" individual option
values through multiple layers of function calls. Instead of:

```cpp
// BAD: Threading individual arguments
void top_level(bool my_flag, int my_value, std::string my_string, ...)
{
  middle_level(my_flag, my_value, my_string, ...);
}

void middle_level(bool my_flag, int my_value, std::string my_string, ...)
{
  bottom_level(my_flag, my_value, my_string, ...);
}

void bottom_level(bool my_flag, int my_value, std::string my_string, ...)
{
  // Finally use the options
}
```

Do this:

```cpp
// GOOD: Pass options object
void top_level(const optionst &options)
{
  middle_level(options);
}

void middle_level(const optionst &options)
{
  bottom_level(options);
}

void bottom_level(const optionst &options)
{
  bool my_flag = options.get_bool_option("my-flag");
  // Use the option
}
```

**Benefits**:
- Cleaner function signatures
- Easier to add new options without changing signatures
- Options are accessed where needed, not passed through layers
- Clear that configuration is immutable (`const` reference)

**When to extract individual values**:

It's acceptable to extract values at a higher level when:
- The lower-level function is a generic utility that shouldn't depend on
  `optionst`
- The option value is being used to select between different algorithms or
  implementations
- You're interfacing with legacy code that predates this pattern

### Step 8: Document Options

**Update the man page** (`doc/man/cbmc.1` or equivalent) for documented options.

For options with complex behavior or non-obvious interactions:

1. **Add code comments** explaining the option's purpose and any subtleties:
   ```cpp
   // The --my-complex-option flag enables X, which requires Y to be
   // configured in a specific way. This is handled by Z function, which...
   if(cmdline.isset("my-complex-option"))
   {
     // ...
   }
   ```

2. **Add to user documentation** (in `doc/cprover-manual/` if appropriate) for
   documented options that need more explanation than fits in help text.

### Step 9: Test Your Option

Ensure your option works correctly:

1. **Add regression tests** in `regression/cbmc/` (or equivalent directory for
   other tools):
   ```
   regression/cbmc/my-new-option/
     test.desc         # Test description and expected behavior
     main.c            # Test input
     test.out          # Expected output
   ```

2. **Test help text**: Run `cbmc --help` and verify your option appears
   correctly (if documented).

3. **Test default behavior**: Ensure the tool works correctly when the option
   is not specified.

4. **Test explicit values**: Test the option with various values, including
   edge cases.

5. **Test interactions**: If your option interacts with others, test those
   combinations.

## Common Patterns and Best Practices

### Setting Default Options

Many tools have a `set_default_options()` method that sets defaults not
determined by command-line parsing:

```cpp
void cbmc_parse_optionst::set_default_options(optionst &options)
{
  // Set options that should always have these defaults
  // unless explicitly overridden
  options.set_option("simplify", true);
  options.set_option("propagation", true);
  // ...
}
```

Call this after creating `optionst` but before using it.

### Option Naming Conventions

- Use lowercase with hyphens: `--my-option` not `--myOption` or `--my_option`
- Use descriptive names: `--bounds-check` not `--bc`
- Prefix negation with `no-`: `--no-bounds-check`
- Be consistent with existing names in the codebase

### Deprecated Options

When deprecating an option:

1. **Keep it functional** (don't break existing scripts)
2. **Remove from help text** (make it undocumented)
3. **Add a warning** when it's used:
   ```cpp
   if(cmdline.isset("deprecated-option"))
   {
     log.warning() << "--deprecated-option is deprecated, use --new-option instead"
                   << messaget::eom;
     // Still handle it for backward compatibility
   }
   ```
4. **Document the deprecation** in CHANGELOG and consider the removal timeline

### Options with Multiple Tools

When adding an option that multiple tools will use:

1. **Create a shared macro** (or extend an existing one)
2. **Share implementation** where possible (e.g., a common function in a
   library)
3. **Ensure consistent behavior** across tools
4. **Document in each tool's help** (using the shared help macro)

## Summary

When adding a new command-line option to CBMC tools:

1. **Question the need** - Minimize options, maximize usability
2. **Define the scope** - Which tools need it? Should it be documented?
3. **Add to option macro** - In `BINARY_parse_options.h` or shared macro
4. **Add to help text** - If documented, add clear description
5. **Handle in config** - If it's a language/platform option, use `configt`
6. **Parse to optionst** - Validate and set in `get_command_line_options()`
7. **Use via optionst** - Pass `const optionst &` to functions that need it
8. **Avoid argument threading** - Don't pass individual option values through
   layers
9. **Document if complex** - Add comments, user docs, and man page entries
10. **Test thoroughly** - Regression tests, edge cases, interactions

By following these guidelines, you'll maintain consistency with the existing
codebase and create options that are easy to use, maintain, and extend.
