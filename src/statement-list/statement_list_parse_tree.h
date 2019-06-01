/*******************************************************************\

Module: Statement List Language Parse Tree

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parse Tree

#ifndef CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSE_TREE_H
#define CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSE_TREE_H

#include <util/std_code.h>
#include <util/std_expr.h>

/// Intermediate representation of a parsed Statement List file before
/// converting it into a goto program. Contains all data structures that are
/// necessary for describing Statement List functions and function blocks.
class statement_list_parse_treet
{
public:
  // Disallow copy construction and copy assignment, but allow move construction
  // and move assignment.
  statement_list_parse_treet(const statement_list_parse_treet &) = delete;
  statement_list_parse_treet &
  operator=(const statement_list_parse_treet &) = delete;
  statement_list_parse_treet(statement_list_parse_treet &&) = default;
  statement_list_parse_treet &
  operator=(statement_list_parse_treet &&) = default;
  statement_list_parse_treet() = default;

  /// Removes all functions and function blocks from the parse tree.
  void clear();

  /// Prints the tree in a human-readable form to the given output stream.
  void output(std::ostream &out) const;

  /// Struct for a single variable declaration in Statement List. Includes
  /// identifier, type and an optional assignment.
  struct var_declarationt
  {
    symbol_exprt variable;
    optionalt<code_assignt> assignment;

    explicit var_declarationt(irep_idt &identifier, typet &type)
      : variable(symbol_exprt(identifier, type))
    {
    }

    /// Prints the declaration in a human-readable form to the given output
    /// stream.
    void output(std::ostream &out) const;
  };
  using var_declarationst = std::list<var_declarationt>;

  /// Represents a regular Statement List instruction which consists out of
  /// one or more codet tokens.
  struct instructiont
  {
    std::vector<codet> tokens;

    /// Adds a codet element to the list of all tokens.
    void add_token(codet &token)
    {
      tokens.push_back(token);
    }

    /// Prints the instruction in a human-readable form to the given output
    /// stream.
    void output(std::ostream &out) const;
  };
  using instructionst = std::list<instructiont>;

  /// Representation of a network in Siemens TIA. Networks are used to divide
  /// multiple Statement List instructions into simpler parts. A function or
  /// function block contains one or more networks. A network can have a title
  /// and may contain zero or more instructions.
  struct networkt
  {
    optionalt<std::string> title;
    instructionst instructions;

    /// Sets the title of the network to a specific value.
    /// \param value: New title. Use an empty string to indicate that there is
    ///   no title.
    void set_title(std::string &value)
    {
      if(value.empty())
        title.reset();
      else
        title = value;
    }

    /// Adds an instruction to the network.
    void add_instruction(instructiont &inst)
    {
      instructions.push_back(inst);
    }

    /// Create the network with a specific \p title.
    explicit networkt(std::string &title)
    {
      set_title(title);
    }

    networkt()
    {
    }

    /// Prints the network in a human-readable form to the given output stream.
    void output(std::ostream &out) const;
  };
  using networkst = std::list<networkt>;

  /// Structure for a simple function in Statement List. Includes fields for
  /// its name, version, variable declarations and networks.
  struct functiont
  {
    // Header
    irep_idt name;
    float version;

    // Variable declarations
    var_declarationst var_input;
    var_declarationst var_inout;
    var_declarationst var_output;

    // Body
    networkst networks;

    /// Create the function \p name with a specific \p version.
    explicit functiont(const irep_idt &name, const float version)
      : name(name), version(version)
    {
    }

    // Disallow copy construction and copy assignment, but allow move
    // construction and move assignment.
    functiont(const functiont &) = delete;
    functiont &operator=(const functiont &) = delete;
    functiont(functiont &&) = default;
    functiont &operator=(functiont &&) = default;

    /// Adds a variable declaration to the list of input variables.
    void add_var_input_entry(var_declarationt &declaration)
    {
      var_input.push_back(declaration);
    }

    /// Adds a variable declaration to the list of inout variables.
    void add_var_inout_entry(var_declarationt &declaration)
    {
      var_inout.push_back(declaration);
    }

    /// Adds a variable declaration to the list of output variables.
    void add_var_output_entry(var_declarationt &declaration)
    {
      var_output.push_back(declaration);
    }

    /// Adds a network to the function.
    void add_network(networkt &network)
    {
      networks.push_back(network);
    }

    /// Prints the function in a human-readable form to the given output
    /// stream.
    virtual void output(std::ostream &out) const;

    // destructor
    virtual ~functiont() = default;
  };
  using functionst = std::list<functiont>;

  /// Structure for a simple function block in Statement List. Includes fields
  /// for its name, version, variable declarations and networks.
  struct function_blockt : functiont
  {
    /// Create the function block \p name with a specific \p version.
    explicit function_blockt(const irep_idt &name, const float version)
      : functiont(name, version)
    {
    }

    // Disallow copy construction and copy assignment, but allow move
    // construction and move assignment.
    function_blockt(const function_blockt &) = delete;
    function_blockt &operator=(const function_blockt &) = delete;
    function_blockt(function_blockt &&) = default;
    function_blockt &operator=(function_blockt &&) = default;

    /// Prints the function block in a human-readable form to the given output
    /// stream.
    void output(std::ostream &out) const override;
  };
  using function_blockst = std::list<function_blockt>;

  /// Adds a function block to the parse tree.
  void add_function_block(function_blockt &block);
  /// Adds a function to the parse tree.
  void add_function(functiont &function);
  /// Swaps the contents of the parse tree with the parameter.
  void swap(statement_list_parse_treet &other);

  // Lists of functions and function blocks.
  function_blockst function_blocks;
  functionst functions;
};

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSE_TREE_H
