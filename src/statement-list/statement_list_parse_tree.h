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
  /// Removes all functions and function blocks from the parse tree.
  void clear();

  /// Struct for a single variable declaration in Statement List. Includes
  /// identifier, type and an optional default value.
  struct var_declarationt
  {
    /// Representation of the variable, including identifier and type.
    symbol_exprt variable;
    /// Optional default value of the variable.
    optionalt<exprt> default_value;

    /// Creates a new. variable declaration.
    /// \param symbol: The variable, including type and name.
    explicit var_declarationt(const symbol_exprt &symbol);
  };
  using var_declarationst = std::list<var_declarationt>;

  /// Represents a regular Statement List instruction which consists out of
  /// one or more codet tokens.
  struct instructiont
  {
    /// Data structure for all tokens of the instruction.
    std::vector<codet> tokens;

    /// Adds a codet element to the list of all tokens.
    /// \param token: Token to be added to the instruction.
    void add_token(const codet &token);
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
    void set_title(const std::string &value);
    /// Adds an instruction to the network.
    void add_instruction(const instructiont &inst);

    /// Create the network with a specific \p title.
    explicit networkt(const std::string &title);

    networkt() = default;
  };
  using networkst = std::list<networkt>;

  /// Base element of all modules in the Totally Integrated Automation (TIA)
  /// portal by Siemens.
  struct tia_modulet
  {
    /// Name of the module.
    const irep_idt name;
    /// Version of the module.
    const std::string version;

    /// Input variable declarations.
    var_declarationst var_input;
    /// Inout variable declarations.
    var_declarationst var_inout;
    /// Output variable declarations.
    var_declarationst var_output;
    /// Temp variable declarations.
    var_declarationst var_temp;
    /// Constant variable declarations.
    var_declarationst var_constant;

    /// List of all networks of this module.
    networkst networks;

    /// Adds a variable declaration to the list of input variables.
    /// \param declaration: Variable declaration to be added.
    void add_var_input_entry(const var_declarationt &declaration);
    /// Adds a variable declaration to the list of inout variables.
    /// \param declaration: Variable declaration to be added.
    void add_var_inout_entry(const var_declarationt &declaration);
    /// Adds a variable declaration to the list of output variables.
    /// \param declaration: Variable declaration to be added.
    void add_var_output_entry(const var_declarationt &declaration);
    /// Adds a variable declaration to the list of temp variables.
    /// \param declaration: Variable declaration to be added.
    void add_var_temp_entry(const var_declarationt &declaration);
    /// Adds a variable declaration to the list of constant variables.
    /// \param declaration: Variable declaration to be added.
    void add_var_constant_entry(const var_declarationt &declaration);
    /// Adds a network to the function.
    /// \param network: Network to be added.
    void add_network(networkt &network);

    /// Create the module \p name with a specific \p version.
    /// \param name: Name of the module.
    /// \param version: Version of the module.
    tia_modulet(const irep_idt &name, const std::string &version);
  };

  /// Structure for a simple function in Statement List. Includes fields for
  /// its name, version, variable declarations and networks.
  struct functiont : tia_modulet
  {
    /// FC-exclusive return type.
    const typet return_type;

    /// Create the function \p name with a specific \p version and a
    /// \p return_value.
    /// \param name: Name of the function.
    /// \param version: Version of the function.
    /// \param return_type: Type of the function's return value.
    functiont(
      const irep_idt &name,
      const std::string &version,
      const typet &return_type);
  };
  using functionst = std::list<functiont>;

  /// Structure for a simple function block in Statement List. Includes fields
  /// for its name, version, variable declarations and networks.
  struct function_blockt : tia_modulet
  {
    /// FB-exclusive static variable declarations.
    var_declarationst var_static;

    /// Create the function block \p name with a specific \p version.
    /// \param name: Name of the function block.
    /// \param version: Version of the function block.
    function_blockt(const irep_idt &name, const std::string &version);

    /// Adds a variable declaration to the list of static variables.
    /// \param declaration: Variable declaration to be added.
    void add_var_static_entry(const var_declarationt &declaration);
  };
  using function_blockst = std::list<function_blockt>;

  /// Adds a function block to the parse tree.
  /// \param block: Function block that should be added to the parse tree.
  void add_function_block(function_blockt &block);
  /// Adds a function to the parse tree.
  /// \param function: Function that should be added to the parse tree.
  void add_function(functiont &function);
  /// Swaps the contents of the parse tree with the parameter.
  /// \param other: Parse tree that should be used in the swap operation.
  void swap(statement_list_parse_treet &other);

  /// List of function blocks this parse tree includes.
  function_blockst function_blocks;
  /// List of functions this parse tree includes.
  functionst functions;
  /// List of tags that were included in the source.
  std::vector<symbol_exprt> tags;
};

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSE_TREE_H
