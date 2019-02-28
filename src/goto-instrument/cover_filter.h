/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Filters for the Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_FILTER_H
#define CPROVER_GOTO_INSTRUMENT_COVER_FILTER_H

#include <regex>
#include <memory>

#include <util/invariant.h>
#include <util/message.h>
#include <util/symbol.h>

#include <goto-programs/goto_model.h>

/// Base class for filtering functions
class function_filter_baset : public messaget
{
public:
  explicit function_filter_baset(message_handlert &message_handler)
    : messaget(message_handler)
  {
  }

  virtual ~function_filter_baset()
  {
  }

  /// Returns true if the function passes the filter criteria
  virtual bool operator()(
    const symbolt &identifier,
    const goto_functionst::goto_functiont &goto_function) const = 0;

  /// Can be called after final filter application to report
  /// on unexpected situations encountered
  virtual void report_anomalies() const
  {
    // do nothing by default
  }
};

/// Base class for filtering goals
class goal_filter_baset : public messaget
{
public:
  explicit goal_filter_baset(message_handlert &message_handler)
    : messaget(message_handler)
  {
  }

  virtual ~goal_filter_baset()
  {
  }

  /// Returns true if the goal passes the filter criteria
  virtual bool operator()(const source_locationt &) const = 0;

  /// Can be called after final filter application to report
  /// on unexpected situations encountered
  virtual void report_anomalies() const
  {
    // do nothing by default
  }
};

/// A collection of function filters to be applied in conjunction
class function_filterst
{
public:
  /// Adds a function filter
  /// \param filter: transfers ownership of filter to the filter collection
  void add(std::unique_ptr<function_filter_baset> filter)
  {
    filters.push_back(std::move(filter));
  }

  /// Applies the filters to the given function
  /// \param identifier: function name
  /// \param goto_function: goto function
  bool operator()(
    const symbolt &identifier,
    const goto_functionst::goto_functiont &goto_function) const
  {
    for(const auto &filter : filters)
      if(!(*filter)(identifier, goto_function))
        return false;

    return true;
  }

  /// Can be called after final filter application to report
  /// on unexpected situations encountered
  void report_anomalies() const
  {
    for(const auto &filter : filters)
      filter->report_anomalies();
  }

private:
  std::vector<std::unique_ptr<function_filter_baset>> filters;
};

/// A collection of goal filters to be applied in conjunction
class goal_filterst
{
public:
  /// Adds a function filter
  /// \param filter: transfers ownership of filter to the filter collection
  void add(std::unique_ptr<goal_filter_baset> filter)
  {
    filters.push_back(std::move(filter));
  }

  /// Applies the filters to the given source location
  /// \param source_location: a source location where a goal is instrumented
  bool operator()(const source_locationt &source_location) const
  {
    for(const auto &filter : filters)
      if(!(*filter)(source_location))
        return false;

    return true;
  }

  /// Can be called after final filter application to report
  /// on unexpected situations encountered
  void report_anomalies() const
  {
    for(const auto &filter : filters)
      filter->report_anomalies();
  }

private:
  std::vector<std::unique_ptr<goal_filter_baset>> filters;
};

/// Filters out CPROVER internal functions
class internal_functions_filtert : public function_filter_baset
{
public:
  explicit internal_functions_filtert(message_handlert &message_handler)
    : function_filter_baset(message_handler)
  {
  }

  bool operator()(
    const symbolt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;
};

class file_filtert : public function_filter_baset
{
public:
  explicit file_filtert(
    message_handlert &message_handler,
    const irep_idt &file_id)
    : function_filter_baset(message_handler), file_id(file_id)
  {
  }

  bool operator()(
    const symbolt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;

private:
  irep_idt file_id;
};

class single_function_filtert : public function_filter_baset
{
public:
  explicit single_function_filtert(
    message_handlert &message_handler,
    const irep_idt &function_id)
    : function_filter_baset(message_handler), function_id(function_id)
  {
  }

  bool operator()(
    const symbolt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;

private:
  irep_idt function_id;
};

/// Filters functions that match the provided pattern
class include_pattern_filtert : public function_filter_baset
{
public:
  explicit include_pattern_filtert(
    message_handlert &message_handler,
    const std::string &cover_include_pattern)
    : function_filter_baset(message_handler),
      regex_matcher(cover_include_pattern)
  {
  }

  bool operator()(
    const symbolt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;

private:
  std::regex regex_matcher;
};

/// Filters out trivial functions
class trivial_functions_filtert : public function_filter_baset
{
public:
  explicit trivial_functions_filtert(message_handlert &message_handler)
    : function_filter_baset(message_handler)
  {
  }

  bool operator()(
    const symbolt &identifier,
    const goto_functionst::goto_functiont &goto_function) const override;
};

/// Filters out goals with source locations considered internal
class internal_goals_filtert : public goal_filter_baset
{
public:
  explicit internal_goals_filtert(message_handlert &message_handler)
    : goal_filter_baset(message_handler)
  {
  }

  bool operator()(const source_locationt &) const override;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_FILTER_H
