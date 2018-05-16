// Author: Diffblue Ltd.

/// \file
/// Java-specific type qualifiers

#ifndef CPROVER_JAVA_BYTECODE_JAVA_QUALIFIERS_H
#define CPROVER_JAVA_BYTECODE_JAVA_QUALIFIERS_H

#include "java_types.h"
#include <ansi-c/c_qualifiers.h>

class java_qualifierst : public c_qualifierst
{
private:
  const namespacet &ns;
  std::vector<java_annotationt> annotations;

public:
  explicit java_qualifierst(const namespacet &ns)
    : ns(ns)
  {}

protected:
  java_qualifierst &operator=(const java_qualifierst &other);
public:
  virtual std::unique_ptr<qualifierst> clone() const override;

  virtual qualifierst &operator+=(const qualifierst &other) override;

  const std::vector<java_annotationt> &get_annotations() const
  {
    return annotations;
  }
  virtual std::size_t count() const override;

  virtual void clear() override;

  virtual void read(const typet &src) override;
  virtual void write(typet &src) const override;

  virtual bool is_subset_of(const qualifierst &other) const override;
  virtual bool operator==(const qualifierst &other) const override;

  virtual std::string as_string() const override;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_QUALIFIERS_H
