// Author: Diffblue Ltd.

/// \file
/// Java-specific type qualifiers

#include "java_qualifiers.h"
#include <sstream>
#include <util/make_unique.h>
#include "expr2java.h"


java_qualifierst &java_qualifierst::operator=(const java_qualifierst &other)
{
  INVARIANT(
    &other.ns == &ns,
    "Can only assign from a java_qualifierst using the same namespace");
  annotations = other.annotations;
  c_qualifierst::operator=(other);
  return *this;
}

java_qualifierst &java_qualifierst::operator=(java_qualifierst &&other)
{
  INVARIANT(
    &other.ns == &ns,
    "Can only assign from a java_qualifierst using the same namespace");
  annotations = std::move(other.annotations);
  c_qualifierst::operator=(other);
  return *this;
}

c_qualifierst &java_qualifierst::operator=(const c_qualifierst &c_other)
{
  auto other = dynamic_cast<const java_qualifierst *>(&c_other);
  if(other != nullptr)
    *this = *other;
  else
  {
    annotations.clear();
    c_qualifierst::operator=(c_other);
  }
  return *this;
}

std::unique_ptr<c_qualifierst> java_qualifierst::clone() const
{
  auto other = util_make_unique<java_qualifierst>(ns);
  *other = *this;
  return std::move(other);
}

std::size_t java_qualifierst::count() const
{
  return c_qualifierst::count() + annotations.size();
}

void java_qualifierst::clear()
{
  c_qualifierst::clear();
  annotations.clear();
}

void java_qualifierst::read(const typet &src)
{
  c_qualifierst::read(src);
  auto &annotated_type = static_cast<const annotated_typet &>(src);
  annotations = annotated_type.get_annotations();
}

void java_qualifierst::write(typet &src) const
{
  c_qualifierst::write(src);
  auto &annotated_type = static_cast<annotated_typet &>(src);
  annotated_type.get_annotations() = annotations;
}

c_qualifierst &java_qualifierst::operator+=(const c_qualifierst &c_other)
{
  c_qualifierst::operator+=(c_other);
  auto other = dynamic_cast<const java_qualifierst *>(&c_other);
  if(other != nullptr)
  {
    std::copy(
      other->annotations.begin(),
      other->annotations.end(),
      std::back_inserter(annotations));
  }
  return *this;
}

bool java_qualifierst::operator==(const c_qualifierst &c_other) const
{
  auto other = dynamic_cast<const java_qualifierst *>(&c_other);
  if(other == nullptr)
    return false;
  return
    c_qualifierst::operator==(c_other) && annotations == other->annotations;
}

bool java_qualifierst::is_subset_of(const c_qualifierst &c_other) const
{
  if(!c_qualifierst::is_subset_of(c_other))
    return false;
  auto other = dynamic_cast<const java_qualifierst *>(&c_other);
  if(other == nullptr)
    return annotations.empty();
  auto &other_a = other->annotations;
  for(const auto &annotation : annotations)
  {
    if(std::find(other_a.begin(), other_a.end(), annotation) == other_a.end())
      return false;
  }
  return true;
}

std::string java_qualifierst::as_string() const
{
  std::stringstream out;
  for(const java_annotationt &annotation : annotations)
  {
    out << '@';
    out << annotation.get_type().subtype().get(ID_identifier);

    if(!annotation.get_values().empty())
    {
      out << '(';

      bool first = true;
      for(const java_annotationt::valuet &value : annotation.get_values())
      {
        if(first)
          first = false;
        else
          out << ", ";

        out << '"' << value.get_name() << '"' << '=';
        out << expr2java(value.get_value(), ns);
      }

      out << ')';
    }
    out << ' ';
  }
  out << c_qualifierst::as_string();
  return out.str();
}
