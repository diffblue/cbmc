// Author: Fotis Koutoulakis for Diffblue Ltd.

#ifndef CPROVER_LIBCPROVER_CPP_OPTIONS_H
#define CPROVER_LIBCPROVER_CPP_OPTIONS_H

#include <memory>

class api_optionst final
{
private:
  /// The values of the options set are stored using the pointer to
  /// implementation pattern (PImpl). This avoids the need for any code which
  /// links to this header to be aware of the size of the implementation struct
  /// or the types contained inside.
  struct implementationt;
  std::unique_ptr<const implementationt> implementation;
  /// Construction is allowed only through the builder.
  explicit api_optionst(std::unique_ptr<const implementationt> implementation);

public:
  class buildert final
  {
  private:
    std::unique_ptr<implementationt> implementation;

  public:
    buildert();
    buildert(buildert &&builder) noexcept;
    ~buildert();

    // Option for expression simplification.
    buildert &simplify(bool on);
    // Option for dropping unused function
    buildert &drop_unused_functions(bool on);
    // Option for validating the goto model
    buildert &validate_goto_model(bool on);

    /// For doing the building when options have been specified.
    api_optionst build();
  };

  // Option for expression simplification.
  bool simplify() const;
  // Option for dropping unused function
  bool drop_unused_functions() const;
  // Option for validating the goto model
  bool validate_goto_model() const;

  api_optionst(api_optionst &&api_options) noexcept;
  api_optionst &operator=(api_optionst &&) noexcept;
  ~api_optionst();
};

#endif
