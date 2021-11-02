/*******************************************************************\

Module: C Wrangler

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// C Wrangler

#include "c_wrangler.h"

#include "c_defines.h"
#include "ctokenit.h"
#include "mini_c_parser.h"

#include <util/cprover_prefix.h>
#include <util/exception_utils.h>
#include <util/file_util.h>
#include <util/json.h>
#include <util/optional.h>
#include <util/prefix.h>
#include <util/run.h>
#include <util/string_utils.h>
#include <util/suffix.h>
#include <util/tempdir.h>

#include <fstream>
#include <iostream>
#include <map>
#include <regex>
#include <sstream>
#include <unordered_map>

struct c_wranglert
{
  // sources and preprocessing
  std::vector<std::string> source_files;
  std::vector<std::string> includes;
  std::vector<std::string> defines;

  // transformations
  struct contract_clauset
  {
    std::string clause;
    std::string content;
    contract_clauset(std::string _clause, std::string _content)
      : clause(std::move(_clause)), content(std::move(_content))
    {
    }
  };

  struct loop_invariantt
  {
    std::string loop_type;
    std::string identifier;
    std::string content;
    loop_invariantt(
      std::string _loop_type,
      std::string _identifier,
      std::string _content)
      : loop_type(std::move(_loop_type)),
        identifier(std::move(_identifier)),
        content(std::move(_content))
    {
    }
  };

  struct assertiont
  {
    std::string identifier;
    std::string content;
    assertiont(std::string _identifier, std::string _content)
      : identifier(std::move(_identifier)), content(std::move(_content))
    {
    }
  };

  struct functiont
  {
    // should be variant to preserve ordering
    std::vector<contract_clauset> contract;
    std::vector<loop_invariantt> loop_invariants;
    std::vector<assertiont> assertions;
    optionalt<std::string> stub;
    bool remove_static = false;
  };

  using functionst = std::list<std::pair<std::regex, functiont>>;
  functionst functions;

  // output
  std::string output;

  void configure_sources(const jsont &);
  void configure_functions(const jsont &);
  void configure_output(const jsont &);
};

void c_wranglert::configure_sources(const jsont &config)
{
  auto sources = config["sources"];

  if(!sources.is_null())
  {
    if(!sources.is_array())
      throw deserialization_exceptiont("sources entry must be sequence");

    for(const auto &source : to_json_array(sources))
    {
      if(!source.is_string())
        throw deserialization_exceptiont("source must be string");

      this->source_files.push_back(source.value);
    }
  }

  auto includes = config["includes"];

  if(!includes.is_null())
  {
    if(!includes.is_array())
      throw deserialization_exceptiont("includes entry must be sequence");

    for(const auto &include : to_json_array(includes))
    {
      if(!include.is_string())
        throw deserialization_exceptiont("include must be string");

      this->includes.push_back(include.value);
    }
  }

  auto defines = config["defines"];

  if(!defines.is_null())
  {
    if(!defines.is_array())
      throw deserialization_exceptiont("defines entry must be sequence");

    for(const auto &define : to_json_array(defines))
    {
      if(!define.is_string())
        throw deserialization_exceptiont("define must be string");

      this->defines.push_back(define.value);
    }
  }
}

void c_wranglert::configure_functions(const jsont &config)
{
  auto functions = config["functions"];

  if(functions.is_null())
    return;

  if(!functions.is_array())
    throw deserialization_exceptiont("functions entry must be sequence");

  for(const auto &function : to_json_array(functions))
  {
    if(!function.is_object())
      throw deserialization_exceptiont("function entry must be object");

    for(const auto &function_entry : to_json_object(function))
    {
      const auto function_name = function_entry.first;
      const auto &items = function_entry.second;

      if(!items.is_array())
        throw deserialization_exceptiont("function entry must be sequence");

      this->functions.emplace_back(function_name, functiont{});
      functiont &function_config = this->functions.back().second;

      for(const auto &function_item : to_json_array(items))
      {
        // These need to start with "ensures", "requires", "assigns",
        // "invariant", "assert", "stub", "remove"
        if(!function_item.is_string())
          throw deserialization_exceptiont("function entry must be string");

        auto item_string = function_item.value;
        auto split = split_string(item_string, ' ');
        if(split.empty())
          continue;

        if(
          split[0] == "ensures" || split[0] == "requires" ||
          split[0] == "assigns")
        {
          std::ostringstream rest;
          join_strings(rest, split.begin() + 1, split.end(), ' ');

          function_config.contract.emplace_back(split[0], rest.str());
        }
        else if(split[0] == "assert" && split.size() >= 3)
        {
          std::ostringstream rest;
          join_strings(rest, split.begin() + 2, split.end(), ' ');

          function_config.assertions.emplace_back(split[1], rest.str());
        }
        else if(
          (split[0] == "for" && split.size() >= 3 && split[2] == "invariant") ||
          (split[0] == "while" && split.size() >= 3 && split[2] == "invariant"))
        {
          std::ostringstream rest;
          join_strings(rest, split.begin() + 3, split.end(), ' ');

          function_config.loop_invariants.emplace_back(
            split[0], split[1], rest.str());
        }
        else if(split[0] == "stub")
        {
          std::ostringstream rest;
          join_strings(rest, split.begin() + 1, split.end(), ' ');

          function_config.stub = rest.str();
        }
        else if(split[0] == "remove")
        {
          if(split.size() == 1)
            throw deserialization_exceptiont("unexpected remove entry");

          if(split[1] == "static")
            function_config.remove_static = true;
          else
            throw deserialization_exceptiont(
              "unexpected remove entry " + split[1]);
        }
        else
          throw deserialization_exceptiont(
            "unexpected function entry " + split[0]);
      }
    }
  }
}

void c_wranglert::configure_output(const jsont &config)
{
  auto output = config["output"];

  if(output.is_null())
    return;

  if(!output.is_string())
    throw deserialization_exceptiont("output entry must be string");

  this->output = output.value;
}

static std::string
preprocess(const std::string &source_file, const c_wranglert &c_wrangler)
{
  std::vector<std::string> argv = {"cc", "-E", source_file};

  for(const auto &include : c_wrangler.includes)
  {
    argv.push_back("-I");
    argv.push_back(include);
  }

  for(const auto &define : c_wrangler.defines)
    argv.push_back(std::string("-D") + define);

  std::ostringstream result;

  auto run_result = run("cc", argv, "", result, "");
  if(run_result != 0)
    throw system_exceptiont("preprocessing " + source_file + " has failed");

  return result.str();
}

static c_definest
get_defines(const std::string &source_file, const c_wranglert &config)
{
  std::vector<std::string> argv = {"cc", "-E", "-dM", source_file};

  for(const auto &include : config.includes)
  {
    argv.push_back("-I");
    argv.push_back(include);
  }

  std::ostringstream result;

  auto run_result = run("cc", argv, "", result, "");
  if(run_result != 0)
    throw system_exceptiont("preprocessing " + source_file + " has failed");

  c_definest defines;
  defines.parse(result.str());
  return defines;
}

static void mangle_function(
  const c_declarationt &declaration,
  const c_definest &defines,
  const c_wranglert::functiont &function_config,
  std::ostream &out)
{
  if(function_config.stub.has_value())
  {
    // replace by stub
    out << function_config.stub.value();
  }
  else
  {
    if(function_config.remove_static)
    {
      for(auto &t : declaration.pre_declarator)
      {
        if(t.text == "static")
        {
          // we replace by white space
          out << std::string(6, ' ');
        }
        else
          out << t.text;
      }
    }
    else
    {
      for(auto &t : declaration.pre_declarator)
        out << t.text;
    }

    for(auto &t : declaration.declarator)
      out << t.text;
    for(auto &t : declaration.post_declarator)
      out << t.text;

    for(const auto &entry : function_config.contract)
      out << ' ' << CPROVER_PREFIX << entry.clause << '('
          << defines(entry.content) << ')';

    std::map<std::string, std::string> loop_invariants;

    for(const auto &entry : function_config.loop_invariants)
      loop_invariants[entry.loop_type + entry.identifier] = entry.content;

    if(loop_invariants.empty())
    {
      for(auto &t : declaration.initializer)
        out << t.text;
    }
    else
    {
      std::size_t for_count = 0, while_count = 0;
      ctokenitt t(declaration.initializer);

      while(t)
      {
        const auto &token = *(t++);
        out << token.text;

        if(token == "while")
        {
          while_count++;
          const auto &invariant =
            loop_invariants["while" + std::to_string(while_count)];

          if(!invariant.empty())
          {
            auto t_end = match_bracket(t, '(', ')');
            for(; t != t_end; t++)
              out << t->text;
            out << ' ' << CPROVER_PREFIX << "loop_invariant("
                << defines(invariant) << ')';
          }
        }
        else if(token == "for")
        {
          for_count++;
          const auto &invariant =
            loop_invariants["for" + std::to_string(for_count)];

          if(!invariant.empty())
          {
            auto t_end = match_bracket(t, '(', ')');
            for(; t != t_end; t++)
              out << t->text;
            out << ' ' << CPROVER_PREFIX << "invariant(" << defines(invariant)
                << ')';
          }
        }
      }
    }
  }
}

static void mangle(
  const c_declarationt &declaration,
  const c_definest &defines,
  const c_wranglert &config,
  std::ostream &out)
{
  auto name_opt = declaration.declared_identifier();
  if(
    declaration.is_function() && name_opt.has_value() && declaration.has_body())
  {
    for(const auto &entry : config.functions)
    {
      if(std::regex_match(name_opt->text, entry.first))
      {
        // we are to modify this function
        mangle_function(declaration, defines, entry.second, out);

        return;
      }
    }
  }

  // output
  out << declaration;
}

static std::string mangle(
  const std::string &in,
  const c_definest &defines,
  const c_wranglert &config)
{
  std::ostringstream out;
  std::istringstream in_str(in);

  auto parsed = parse_c(in_str);

  for(const auto &declaration : parsed)
    mangle(declaration, defines, config, out);

  return out.str();
}

void c_wrangler(const jsont &config)
{
  c_wranglert c_wrangler;

  c_wrangler.configure_sources(config);
  c_wrangler.configure_functions(config);
  c_wrangler.configure_output(config);

  for(auto &source_file : c_wrangler.source_files)
  {
    // first preprocess
    auto preprocessed = preprocess(source_file, c_wrangler);

    // get the defines
    auto defines = get_defines(source_file, c_wrangler);

    // now mangle
    auto mangled = mangle(preprocessed, defines, c_wrangler);

    // now output
    if(c_wrangler.output == "stdout" || c_wrangler.output.empty())
    {
      std::cout << mangled;
    }
    else
    {
      std::ofstream out(c_wrangler.output);
      out << mangled;
    }
  }
}
