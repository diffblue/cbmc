/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#include "java_bytecode_convert_class.h"

#ifdef DEBUG
#include <iostream>
#endif

#include "java_root_class.h"
#include "java_types.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_language.h"
#include "java_utils.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/suffix.h>

class java_bytecode_convert_classt:public messaget
{
public:
  java_bytecode_convert_classt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    size_t _max_array_length,
    method_bytecodet &method_bytecode,
    java_string_library_preprocesst &_string_preprocess,
    const std::unordered_set<std::string> &no_load_classes)
    : messaget(_message_handler),
      symbol_table(_symbol_table),
      max_array_length(_max_array_length),
      method_bytecode(method_bytecode),
      string_preprocess(_string_preprocess),
      no_load_classes(no_load_classes)
  {
  }

  /// Converts all the class parse trees into a class symbol and adds it to the
  /// symbol table.
  /// \param parse_trees: The parse trees found for the class to be converted.
  /// \remarks
  ///   Allows multiple definitions of the same class to appear on the
  ///   classpath, so long as all but the first definition are marked with the
  ///   attribute `\@java::org.cprover.OverlayClassImplementation`.
  ///   Overlay class definitions can contain methods with the same signature
  ///   as methods in the original class, so long as these are marked with the
  ///   attribute `\@java::org.cprover.OverlayMethodImplementation`; such
  ///   overlay methods are replaced in the original file with the version
  ///   found in the last overlay on the classpath. Later definitions can
  ///   also contain new supporting methods and fields that are merged in.
  ///   This will allow insertion of Java methods into library classes to
  ///   handle, for example, modelling dependency injection.
  void operator()(
    const java_class_loadert::parse_tree_with_overlayst &parse_trees)
  {
    PRECONDITION(!parse_trees.empty());
    const java_bytecode_parse_treet &parse_tree = parse_trees.front();

    // Add array types to the symbol table
    add_array_types(symbol_table);

    const bool loading_success =
      parse_tree.loading_successful &&
      !no_load_classes.count(id2string(parse_tree.parsed_class.name));
    if(loading_success)
    {
      overlay_classest overlay_classes;
      for(auto overlay_class_it = std::next(parse_trees.begin());
          overlay_class_it != parse_trees.end();
          ++overlay_class_it)
      {
        overlay_classes.push_front(std::cref(overlay_class_it->parsed_class));
      }
      convert(parse_tree.parsed_class, overlay_classes);
    }

    // Add as string type if relevant
    const irep_idt &class_name = parse_tree.parsed_class.name;
    if(string_preprocess.is_known_string_type(class_name))
      string_preprocess.add_string_type(class_name, symbol_table);
    else if(!loading_success)
      // Generate stub if couldn't load from bytecode and wasn't string type
      generate_class_stub(
        class_name,
        symbol_table,
        get_message_handler(),
        struct_union_typet::componentst{});
  }

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::fieldt fieldt;
  typedef java_bytecode_parse_treet::methodt methodt;
  typedef java_bytecode_parse_treet::annotationt annotationt;

private:
  symbol_tablet &symbol_table;
  const size_t max_array_length;
  method_bytecodet &method_bytecode;
  java_string_library_preprocesst &string_preprocess;

  // conversion
  typedef std::list<std::reference_wrapper<const classt>> overlay_classest;
  void convert(const classt &c, const overlay_classest &overlay_classes);
  void convert(symbolt &class_symbol, const fieldt &f);

  // see definition below for more info
  static void add_array_types(symbol_tablet &symbol_table);

  /// Check if a method is an overlay method by searching for
  /// `ID_overlay_method` in its list of annotations.
  ///
  /// An overlay method is a method with the annotation
  /// \@OverlayMethodImplementation. They should only appear in
  /// [overlay classes](\ref java_class_loader.cpp::is_overlay_class). They
  /// will be loaded by JBMC instead of the method with the same signature
  /// in the underlying class. It is an error if there is no method with the
  /// same signature in the underlying class. It is an error if a method in
  /// an overlay class has the same signature as a method in the underlying
  /// class and it isn't marked as an overlay method or an
  /// [ignored method](\ref java_bytecode_convert_classt::is_ignored_method).
  ///
  /// \param method: a `methodt` object from a java bytecode parse tree
  /// \return true if the method is an overlay method, else false
  static bool is_overlay_method(const methodt &method)
  {
    return method.has_annotation(ID_overlay_method);
  }

  /// Check if a method is an ignored method by searching for
  /// `ID_ignored_method` in its list of annotations.
  ///
  /// An ignored method is a method with the annotation
  /// \@IgnoredMethodImplementation. They will be ignored by JBMC. They are
  /// intended for use in
  /// [overlay classes](\ref java_class_loader.cpp::is_overlay_class), in
  /// particular for methods which must exist in the overlay class so that
  /// it will compile, e.g. default constructors, but which we do not want
  /// to overlay the corresponding method in the
  /// underlying class. It is an error if a method in
  /// an overlay class has the same signature as a method in the underlying
  /// class and it isn't marked as an
  /// [overlay method](\ref java_bytecode_convert_classt::is_overlay_method)
  /// or an ignored method.
  ///
  /// \param method: a `methodt` object from a java bytecode parse tree
  /// \return true if the method is an ignored method, else false
  static bool is_ignored_method(const methodt &method)
  {
    return method.has_annotation(ID_ignored_method);
  }

  bool check_field_exists(
    const fieldt &field,
    const irep_idt &qualified_fieldname,
    const struct_union_typet::componentst &fields) const;

  std::unordered_set<std::string> no_load_classes;
};

/// Auxiliary function to extract the generic superclass reference from the
/// class signature. If the signature is empty or the superclass is not generic
/// it returns empty.
/// Example:
/// - class: A<T> extends B<T, Integer> implements C, D<T>
/// - signature: <T:Ljava/lang/Object;>B<TT;Ljava/lang/Integer;>;LC;LD<TT;>;
/// - returned superclass reference: B<TT;Ljava/lang/Integer;>;
/// \param signature: Signature of the class
/// \return Reference of the generic superclass, or empty if the superclass
///   is not generic
static optionalt<std::string>
extract_generic_superclass_reference(const optionalt<std::string> &signature)
{
  if(signature.has_value())
  {
    // skip the (potential) list of generic parameters at the beginning of the
    // signature
    const size_t start =
      signature.value().front() == '<'
        ? find_closing_delimiter(signature.value(), 0, '<', '>') + 1
        : 0;

    // extract the superclass reference
    const size_t end =
      find_closing_semi_colon_for_reference_type(signature.value(), start);
    const std::string superclass_ref =
      signature.value().substr(start, (end - start) + 1);

    // if the superclass is generic then the reference is of form
    // `Lsuperclass-name<generic-types;>;` if it is implicitly generic, then the
    // reference is of the form
    // `Lsuperclass-name<Tgeneric-types;>.Innerclass-Name`
    if(superclass_ref.find('<') != std::string::npos)
      return superclass_ref;
  }
  return {};
}

/// Auxiliary function to extract the generic interface reference of an
/// interface with the specified name from the class signature. If the
/// signature is empty or the interface is not generic it returns empty.
/// Example:
/// - class: A<T> extends B<T, Integer> implements C, D<T>
/// - signature: <T:Ljava/lang/Object;>B<TT;Ljava/lang/Integer;>;LC;LD<TT;>;
/// - returned interface reference for C: LC;
/// - returned interface reference for D: LD<TT;>;
/// \param signature: Signature of the class
/// \param interface_name: The interface name
/// \return Reference of the generic interface, or empty if the interface
///   is not generic
static optionalt<std::string> extract_generic_interface_reference(
  const optionalt<std::string> &signature,
  const std::string &interface_name)
{
  if(signature.has_value())
  {
    // skip the (potential) list of generic parameters at the beginning of the
    // signature
    size_t start =
      signature.value().front() == '<'
        ? find_closing_delimiter(signature.value(), 0, '<', '>') + 1
        : 0;

    // skip the superclass reference (if there is at least one interface
    // reference in the signature, then there is a superclass reference)
    start =
      find_closing_semi_colon_for_reference_type(signature.value(), start) + 1;

    // if the interface name includes package name, convert dots to slashes
    std::string interface_name_slash_to_dot = interface_name;
    std::replace(
      interface_name_slash_to_dot.begin(),
      interface_name_slash_to_dot.end(),
      '.',
      '/');

    start =
      signature.value().find("L" + interface_name_slash_to_dot + "<", start);
    if(start != std::string::npos)
    {
      const size_t &end =
        find_closing_semi_colon_for_reference_type(signature.value(), start);
      return signature.value().substr(start, (end - start) + 1);
    }
  }
  return {};
}

/// Convert a class, adding symbols to the symbol table for its members
/// \param c: Bytecode of the class to convert
/// \param overlay_classes: Bytecode of any overlays for the class to convert
void java_bytecode_convert_classt::convert(
  const classt &c,
  const overlay_classest &overlay_classes)
{
  std::string qualified_classname="java::"+id2string(c.name);
  if(symbol_table.has_symbol(qualified_classname))
  {
    debug() << "Skip class " << c.name << " (already loaded)" << eom;
    return;
  }

  java_class_typet class_type;
  if(c.signature.has_value() && c.signature.value()[0]=='<')
  {
    java_generic_class_typet generic_class_type;
#ifdef DEBUG
    std::cout << "INFO: found generic class signature "
              << c.signature.value()
              << " in parsed class "
              << c.name << "\n";
#endif
    try
    {
      const std::vector<typet> &generic_types=java_generic_type_from_string(
        id2string(c.name),
        c.signature.value());
      for(const typet &t : generic_types)
      {
        generic_class_type.generic_types()
          .push_back(to_java_generic_parameter(t));
      }
      class_type=generic_class_type;
    }
    catch(const unsupported_java_class_signature_exceptiont &e)
    {
      warning() << "Class: " << c.name
                << "\n could not parse signature: " << c.signature.value()
                << "\n " << e.what() << "\n ignoring that the class is generic"
                << eom;
    }
  }

  class_type.set_tag(c.name);
  class_type.set_inner_name(c.inner_name);
  class_type.set(ID_abstract, c.is_abstract);
  class_type.set(ID_is_annotation, c.is_annotation);
  class_type.set(ID_interface, c.is_interface);
  class_type.set(ID_synthetic, c.is_synthetic);
  class_type.set_final(c.is_final);
  class_type.set_is_inner_class(c.is_inner_class);
  class_type.set_is_static_class(c.is_static_class);
  class_type.set_is_anonymous_class(c.is_anonymous_class);
  class_type.set_outer_class(c.outer_class);
  class_type.set_super_class(c.super_class);
  if(c.is_enum)
  {
    if(max_array_length != 0 && c.enum_elements > max_array_length)
    {
      warning() << "Java Enum " << c.name << " won't work properly because max "
                << "array length (" << max_array_length << ") is less than the "
                << "enum size (" << c.enum_elements << ")" << eom;
    }
    class_type.set(
      ID_java_enum_static_unwind,
      std::to_string(c.enum_elements+1));
    class_type.set(ID_enumeration, true);
  }

  if(c.is_public)
    class_type.set_access(ID_public);
  else if(c.is_protected)
    class_type.set_access(ID_protected);
  else if(c.is_private)
    class_type.set_access(ID_private);
  else
    class_type.set_access(ID_default);

  if(!c.super_class.empty())
  {
    const struct_tag_typet base("java::" + id2string(c.super_class));

    // if the superclass is generic then the class has the superclass reference
    // including the generic info in its signature
    // e.g., signature for class 'A<T>' that extends
    // 'Generic<Integer>' is '<T:Ljava/lang/Object;>LGeneric<LInteger;>;'
    const optionalt<std::string> &superclass_ref =
      extract_generic_superclass_reference(c.signature);
    if(superclass_ref.has_value())
    {
      try
      {
        const java_generic_struct_tag_typet generic_base(
          base, superclass_ref.value(), qualified_classname);
        class_type.add_base(generic_base);
      }
      catch(const unsupported_java_class_signature_exceptiont &e)
      {
        warning() << "Superclass: " << c.super_class << " of class: " << c.name
                  << "\n could not parse signature: " << superclass_ref.value()
                  << "\n " << e.what()
                  << "\n ignoring that the superclass is generic" << eom;
        class_type.add_base(base);
      }
    }
    else
    {
      class_type.add_base(base);
    }
    class_typet::componentt base_class_field;
    base_class_field.type() = class_type.bases().at(0).type();
    base_class_field.set_name("@" + id2string(c.super_class));
    base_class_field.set_base_name("@" + id2string(c.super_class));
    base_class_field.set_pretty_name("@" + id2string(c.super_class));
    class_type.components().push_back(base_class_field);
  }

  // interfaces are recorded as bases
  for(const auto &interface : c.implements)
  {
    const struct_tag_typet base("java::" + id2string(interface));

    // if the interface is generic then the class has the interface reference
    // including the generic info in its signature
    // e.g., signature for class 'A implements GenericInterface<Integer>' is
    // 'Ljava/lang/Object;LGenericInterface<LInteger;>;'
    const optionalt<std::string> interface_ref =
      extract_generic_interface_reference(c.signature, id2string(interface));
    if(interface_ref.has_value())
    {
      try
      {
        const java_generic_struct_tag_typet generic_base(
          base, interface_ref.value(), qualified_classname);
        class_type.add_base(generic_base);
      }
      catch(const unsupported_java_class_signature_exceptiont &e)
      {
        warning() << "Interface: " << interface << " of class: " << c.name
                  << "\n could not parse signature: " << interface_ref.value()
                  << "\n " << e.what()
                  << "\n ignoring that the interface is generic" << eom;
        class_type.add_base(base);
      }
    }
    else
    {
      class_type.add_base(base);
    }
  }

  // now do lambda method handles (bootstrap methods)
  for(const auto &lambda_entry : c.lambda_method_handle_map)
  {
    // if the handle is of unknown type, we still need to store it to preserve
    // the correct indexing (invokedynamic instructions will retrieve
    // method handles by index)
    lambda_entry.second.is_unknown_handle()
      ? class_type.add_unknown_lambda_method_handle()
      : class_type.add_lambda_method_handle(
          "java::" + id2string(lambda_entry.second.lambda_method_ref));
  }

  // Load annotations
  if(!c.annotations.empty())
    convert_annotations(c.annotations, class_type.get_annotations());

  // the base name is the name of the class without the package
  const irep_idt base_name = [](const std::string &full_name) {
    const size_t last_dot = full_name.find_last_of('.');
    return last_dot == std::string::npos
             ? full_name
             : std::string(full_name, last_dot + 1, std::string::npos);
  }(id2string(c.name));

  // produce class symbol
  symbolt new_symbol;
  new_symbol.base_name = base_name;
  new_symbol.pretty_name=c.name;
  new_symbol.name=qualified_classname;
  class_type.set_name(new_symbol.name);
  new_symbol.type=class_type;
  new_symbol.mode=ID_java;
  new_symbol.is_type=true;

  symbolt *class_symbol;

  // add before we do members
  debug() << "Adding symbol: class '" << c.name << "'" << eom;
  if(symbol_table.move(new_symbol, class_symbol))
  {
    error() << "failed to add class symbol " << new_symbol.name << eom;
    throw 0;
  }

  // Now do fields
  const class_typet::componentst &fields =
    to_class_type(class_symbol->type).components();
  // Include fields from overlay classes as they will be required by the
  // methods defined there
  for(auto overlay_class : overlay_classes)
  {
    for(const auto &field : overlay_class.get().fields)
    {
      std::string field_id = qualified_classname + "." + id2string(field.name);
      if(check_field_exists(field, field_id, fields))
      {
        std::string err =
          "Duplicate field definition for " + field_id + " in overlay class";
        // TODO: This could just be a warning if the types match
        error() << err << eom;
        throw err.c_str();
      }
      debug()
        << "Adding symbol from overlay class:  field '" << field.name << "'"
        << eom;
      convert(*class_symbol, field);
      POSTCONDITION(check_field_exists(field, field_id, fields));
    }
  }
  for(const auto &field : c.fields)
  {
    std::string field_id = qualified_classname + "." + id2string(field.name);
    if(check_field_exists(field, field_id, fields))
    {
      // TODO: This could be a warning if the types match
      error()
        << "Field definition for " << field_id
        << " already loaded from overlay class" << eom;
      continue;
    }
    debug() << "Adding symbol:  field '" << field.name << "'" << eom;
    convert(*class_symbol, field);
    POSTCONDITION(check_field_exists(field, field_id, fields));
  }

  // Now do methods
  std::set<irep_idt> overlay_methods;
  for(auto overlay_class : overlay_classes)
  {
    for(const methodt &method : overlay_class.get().methods)
    {
      const irep_idt method_identifier =
        qualified_classname + "." + id2string(method.name)
          + ":" + method.descriptor;
      if(is_ignored_method(method))
      {
        debug()
          << "Ignoring method:  '" << method_identifier << "'"
          << eom;
        continue;
      }
      if(method_bytecode.contains_method(method_identifier))
      {
        // This method has already been discovered and added to method_bytecode
        // while parsing an overlay class that appears later in the classpath
        // (we're working backwards)
        // Warn the user if the definition already found was not an overlay,
        // otherwise simply don't load this earlier definition
        if(overlay_methods.count(method_identifier) == 0)
        {
          // This method was defined in a previous class definition without
          // being marked as an overlay method
          warning()
            << "Method " << method_identifier
            << " exists in an overlay class without being marked as an "
              "overlay and also exists in another overlay class that appears "
              "earlier in the classpath"
            << eom;
        }
        continue;
      }
      // Always run the lazy pre-stage, as it symbol-table
      // registers the function.
      debug()
        << "Adding symbol from overlay class:  method '" << method_identifier
        << "'" << eom;
      java_bytecode_convert_method_lazy(
        *class_symbol,
        method_identifier,
        method,
        symbol_table,
        get_message_handler());
      method_bytecode.add(qualified_classname, method_identifier, method);
      if(is_overlay_method(method))
        overlay_methods.insert(method_identifier);
    }
  }
  for(const methodt &method : c.methods)
  {
    const irep_idt method_identifier=
      qualified_classname + "." + id2string(method.name)
        + ":" + method.descriptor;
    if(is_ignored_method(method))
    {
      debug()
        << "Ignoring method:  '" << method_identifier << "'"
        << eom;
      continue;
    }
    if(method_bytecode.contains_method(method_identifier))
    {
      // This method has already been discovered while parsing an overlay
      // class
      // If that definition is an overlay then we simply don't load this
      // original definition and we remove it from the list of overlays
      if(overlay_methods.erase(method_identifier) == 0)
      {
        // This method was defined in a previous class definition without
        // being marked as an overlay method
        warning()
          << "Method " << method_identifier
          << " exists in an overlay class without being marked as an overlay "
            "and also exists in the underlying class"
          << eom;
      }
      continue;
    }
    // Always run the lazy pre-stage, as it symbol-table
    // registers the function.
    debug() << "Adding symbol:  method '" << method_identifier << "'" << eom;
    java_bytecode_convert_method_lazy(
      *class_symbol,
      method_identifier,
      method,
      symbol_table,
      get_message_handler());
    method_bytecode.add(qualified_classname, method_identifier, method);
    if(is_overlay_method(method))
    {
      warning()
        << "Method " << method_identifier
        << " marked as an overlay where defined in the underlying class" << eom;
    }
  }
  if(!overlay_methods.empty())
  {
    error()
      << "Overlay methods defined in overlay classes did not exist in the "
        "underlying class:\n";
    for(const irep_idt &method_id : overlay_methods)
      error() << "  " << method_id << "\n";
    error() << eom;
  }

  // is this a root class?
  if(c.super_class.empty())
    java_root_class(*class_symbol);
}

bool java_bytecode_convert_classt::check_field_exists(
  const java_bytecode_parse_treet::fieldt &field,
  const irep_idt &qualified_fieldname,
  const struct_union_typet::componentst &fields) const
{
  if(field.is_static)
    return symbol_table.has_symbol(qualified_fieldname);

  auto existing_field = std::find_if(
    fields.begin(),
    fields.end(),
    [&field](const struct_union_typet::componentt &f)
    {
      return f.get_name() == field.name;
    });
  return existing_field != fields.end();
}

/// Convert a field, adding a symbol to teh symbol table for it
/// \param class_symbol: The already added symbol for the containing class
/// \param f: The bytecode for the field to convert
void java_bytecode_convert_classt::convert(
  symbolt &class_symbol,
  const fieldt &f)
{
  typet field_type;
  if(f.signature.has_value())
  {
    field_type=java_type_from_string_with_exception(
      f.descriptor,
      f.signature,
      id2string(class_symbol.name));

    /// this is for a free type variable, e.g., a field of the form `T f;`
    if(is_java_generic_parameter(field_type))
    {
#ifdef DEBUG
      std::cout << "fieldtype: generic "
                << to_java_generic_parameter(field_type).type_variable()
                     .get_identifier()
                << " name " << f.name << "\n";
#endif
    }

    /// this is for a field that holds a generic type, either with instantiated
    /// or with free type variables, e.g., `List<T> l;` or `List<Integer> l;`
    else if(is_java_generic_type(field_type))
    {
      java_generic_typet &with_gen_type=
        to_java_generic_type(field_type);
#ifdef DEBUG
      std::cout << "fieldtype: generic container type "
                << std::to_string(with_gen_type.generic_type_arguments().size())
                << " type " << with_gen_type.id()
                << " name " << f.name
                << " subtype id " << with_gen_type.subtype().id() << "\n";
#endif
      field_type=with_gen_type;
    }
  }
  else
    field_type=java_type_from_string(f.descriptor);

  // is this a static field?
  if(f.is_static)
  {
    // Create the symbol; we won't add to the struct type.
    symbolt new_symbol;

    new_symbol.is_static_lifetime=true;
    new_symbol.is_lvalue=true;
    new_symbol.is_state_var=true;
    new_symbol.name=id2string(class_symbol.name)+"."+id2string(f.name);
    new_symbol.base_name=f.name;
    new_symbol.type=field_type;
    // Annotating the type with ID_C_class to provide a static field -> class
    // link matches the method used by java_bytecode_convert_method::convert
    // for methods.
    new_symbol.type.set(ID_C_class, class_symbol.name);
    new_symbol.type.set(ID_C_field, f.name);
    new_symbol.type.set(ID_C_constant, f.is_final);
    new_symbol.pretty_name=id2string(class_symbol.pretty_name)+
      "."+id2string(f.name);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;

    // These annotations use `ID_C_access` instead of `ID_access` like methods
    // to avoid type clashes in expressions like `some_static_field = 0`, where
    // with ID_access the constant '0' would need to have an access modifier
    // too, or else appear to have incompatible type.
    if(f.is_public)
      new_symbol.type.set(ID_C_access, ID_public);
    else if(f.is_protected)
      new_symbol.type.set(ID_C_access, ID_protected);
    else if(f.is_private)
      new_symbol.type.set(ID_C_access, ID_private);
    else
      new_symbol.type.set(ID_C_access, ID_default);

    const namespacet ns(symbol_table);
    const auto value = zero_initializer(field_type, class_symbol.location, ns);
    if(!value.has_value())
    {
      error().source_location = class_symbol.location;
      error() << "failed to zero-initialize " << f.name << eom;
      throw 0;
    }
    new_symbol.value = *value;

    // Load annotations
    if(!f.annotations.empty())
    {
      convert_annotations(
        f.annotations,
        type_checked_cast<annotated_typet>(new_symbol.type).get_annotations());
    }

    // Do we have the static field symbol already?
    const auto s_it=symbol_table.symbols.find(new_symbol.name);
    if(s_it!=symbol_table.symbols.end())
      symbol_table.erase(s_it); // erase, we stubbed it

    if(symbol_table.add(new_symbol))
      assert(false && "failed to add static field symbol");
  }
  else
  {
    class_typet &class_type=to_class_type(class_symbol.type);

    class_type.components().emplace_back();
    class_typet::componentt &component=class_type.components().back();

    component.set_name(f.name);
    component.set_base_name(f.name);
    component.set_pretty_name(f.name);
    component.type()=field_type;

    if(f.is_private)
      component.set_access(ID_private);
    else if(f.is_protected)
      component.set_access(ID_protected);
    else if(f.is_public)
      component.set_access(ID_public);
    else
      component.set_access(ID_default);

    component.set_is_final(f.is_final);

    // Load annotations
    if(!f.annotations.empty())
    {
      convert_annotations(
        f.annotations,
        static_cast<annotated_typet &>(component.type()).get_annotations());
    }
  }
}

/// Register in the \p symbol_table new symbols for the objects
/// java::array[X] where X is byte, float, int, char...
void java_bytecode_convert_classt::add_array_types(symbol_tablet &symbol_table)
{
  const std::string letters="ijsbcfdza";

  for(const char l : letters)
  {
    struct_tag_typet struct_tag_type =
      to_struct_tag_type(java_array_type(l).subtype());

    const irep_idt &struct_tag_type_identifier =
      struct_tag_type.get_identifier();
    if(symbol_table.has_symbol(struct_tag_type_identifier))
      return;

    java_class_typet class_type;
    // we have the base class, java.lang.Object, length and data
    // of appropriate type
    class_type.set_tag(struct_tag_type_identifier);
    // Note that non-array types don't have "java::" at the beginning of their
    // tag, and their name is "java::" + their tag. Since arrays do have
    // "java::" at the beginning of their tag we set the name to be the same as
    // the tag.
    class_type.set_name(struct_tag_type_identifier);

    class_type.components().reserve(3);
    class_typet::componentt base_class_component(
      "@java.lang.Object", struct_tag_typet("java::java.lang.Object"));
    base_class_component.set_pretty_name("@java.lang.Object");
    base_class_component.set_base_name("@java.lang.Object");
    class_type.components().push_back(base_class_component);

    class_typet::componentt length_component("length", java_int_type());
    length_component.set_pretty_name("length");
    length_component.set_base_name("length");
    class_type.components().push_back(length_component);

    class_typet::componentt data_component(
      "data", java_reference_type(java_type_from_char(l)));
    data_component.set_pretty_name("data");
    data_component.set_base_name("data");
    class_type.components().push_back(data_component);

    class_type.add_base(struct_tag_typet("java::java.lang.Object"));

    INVARIANT(
      is_valid_java_array(class_type),
      "Constructed a new type representing a Java Array "
      "object that doesn't match expectations");

    symbolt symbol;
    symbol.name = struct_tag_type_identifier;
    symbol.base_name = struct_tag_type.get(ID_C_base_name);
    symbol.is_type=true;
    symbol.type = class_type;
    symbol.mode = ID_java;
    symbol_table.add(symbol);

    // Also provide a clone method:
    // ----------------------------

    const irep_idt clone_name =
      id2string(struct_tag_type_identifier) + ".clone:()Ljava/lang/Object;";
    java_method_typet::parametert this_param;
    this_param.set_identifier(id2string(clone_name)+"::this");
    this_param.set_base_name(ID_this);
    this_param.set_this();
    this_param.type() = java_reference_type(struct_tag_type);
    const java_method_typet clone_type({this_param}, java_lang_object_type());

    parameter_symbolt this_symbol;
    this_symbol.name=this_param.get_identifier();
    this_symbol.base_name=this_param.get_base_name();
    this_symbol.pretty_name=this_symbol.base_name;
    this_symbol.type=this_param.type();
    this_symbol.mode=ID_java;
    symbol_table.add(this_symbol);

    const irep_idt local_name=
      id2string(clone_name)+"::cloned_array";
    auxiliary_symbolt local_symbol;
    local_symbol.name=local_name;
    local_symbol.base_name="cloned_array";
    local_symbol.pretty_name=local_symbol.base_name;
    local_symbol.type = java_reference_type(struct_tag_type);
    local_symbol.mode=ID_java;
    symbol_table.add(local_symbol);
    const auto &local_symexpr=local_symbol.symbol_expr();

    code_declt declare_cloned(local_symexpr);

    source_locationt location;
    location.set_function(local_name);
    side_effect_exprt java_new_array(
      ID_java_new_array, java_reference_type(struct_tag_type), location);
    dereference_exprt old_array(this_symbol.symbol_expr(), struct_tag_type);
    dereference_exprt new_array(local_symexpr, struct_tag_type);
    member_exprt old_length(
      old_array, length_component.get_name(), length_component.type());
    java_new_array.copy_to_operands(old_length);
    code_assignt create_blank(local_symexpr, java_new_array);

    member_exprt old_data(
      old_array, data_component.get_name(), data_component.type());
    member_exprt new_data(
      new_array, data_component.get_name(), data_component.type());

    /*
      // TODO use this instead of a loop.
    codet array_copy;
    array_copy.set_statement(ID_array_copy);
    array_copy.move_to_operands(new_data);
    array_copy.move_to_operands(old_data);
    clone_body.move_to_operands(array_copy);
    */

    // Begin for-loop to replace:

    const irep_idt index_name=
      id2string(clone_name)+"::index";
    auxiliary_symbolt index_symbol;
    index_symbol.name=index_name;
    index_symbol.base_name="index";
    index_symbol.pretty_name=index_symbol.base_name;
    index_symbol.type = length_component.type();
    index_symbol.mode=ID_java;
    symbol_table.add(index_symbol);
    const auto &index_symexpr=index_symbol.symbol_expr();

    code_declt declare_index(index_symexpr);

    side_effect_exprt inc(ID_assign, typet(), location);
    inc.operands().resize(2);
    inc.op0()=index_symexpr;
    inc.op1()=plus_exprt(index_symexpr, from_integer(1, index_symexpr.type()));

    dereference_exprt old_cell(
      plus_exprt(old_data, index_symexpr), old_data.type().subtype());
    dereference_exprt new_cell(
      plus_exprt(new_data, index_symexpr), new_data.type().subtype());

    const code_fort copy_loop(
      code_assignt(index_symexpr, from_integer(0, index_symexpr.type())),
      binary_relation_exprt(index_symexpr, ID_lt, old_length),
      std::move(inc),
      code_assignt(std::move(new_cell), std::move(old_cell)));

    member_exprt new_base_class(
      new_array, base_class_component.get_name(), base_class_component.type());
    address_of_exprt retval(new_base_class);
    code_returnt return_inst(retval);

    const code_blockt clone_body(
      {declare_cloned, create_blank, declare_index, copy_loop, return_inst});

    symbolt clone_symbol;
    clone_symbol.name=clone_name;
    clone_symbol.pretty_name =
      id2string(struct_tag_type_identifier) + ".clone:()";
    clone_symbol.base_name="clone";
    clone_symbol.type=clone_type;
    clone_symbol.value=clone_body;
    clone_symbol.mode=ID_java;
    symbol_table.add(clone_symbol);
  }
}

bool java_bytecode_convert_class(
  const java_class_loadert::parse_tree_with_overlayst &parse_trees,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  method_bytecodet &method_bytecode,
  java_string_library_preprocesst &string_preprocess,
  const std::unordered_set<std::string> &no_load_classes)
{
  java_bytecode_convert_classt java_bytecode_convert_class(
    symbol_table,
    message_handler,
    max_array_length,
    method_bytecode,
    string_preprocess,
    no_load_classes);

  try
  {
    java_bytecode_convert_class(parse_trees);
    return false;
  }

  catch(int)
  {
  }

  catch(const char *e)
  {
    java_bytecode_convert_class.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    java_bytecode_convert_class.error() << e << messaget::eom;
  }

  return true;
}

/// For a given generic type parameter, check if there is a parameter in the
/// given vector of replacement parameters with a matching name. If yes,
/// replace the identifier of the parameter at hand by the identifier of
/// the matching parameter.
/// Example: if \p parameter has identifier `java::Outer$Inner::T` and
/// there is a replacement parameter with identifier `java::Outer::T`, the
/// identifier of \p parameter gets set to `java::Outer::T`.
/// \param parameter: The given generic type parameter
/// \param replacement_parameters: vector of generic parameters (only viable
///   ones, i.e., only those that can actually appear here such as generic
///   parameters of outer classes of the class specified by the prefix of \p
///   parameter identifier)
static void find_and_replace_parameter(
  java_generic_parametert &parameter,
  const std::vector<java_generic_parametert> &replacement_parameters)
{
  // get the name of the parameter, e.g., `T` from `java::Class::T`
  const std::string &parameter_full_name =
    id2string(parameter.type_variable_ref().get_identifier());
  const std::string &parameter_name =
    parameter_full_name.substr(parameter_full_name.rfind("::") + 2);

  // check if there is a replacement parameter with the same name
  const auto replacement_parameter_p = std::find_if(
    replacement_parameters.begin(),
    replacement_parameters.end(),
    [&parameter_name](const java_generic_parametert &replacement_param)
    {
      const std::string &replacement_parameter_full_name =
        id2string(replacement_param.type_variable().get_identifier());
      return parameter_name.compare(
               replacement_parameter_full_name.substr(
                 replacement_parameter_full_name.rfind("::") + 2)) == 0;
    });

  // if a replacement parameter was found, update the identifier
  if(replacement_parameter_p != replacement_parameters.end())
  {
    const std::string &replacement_parameter_full_name =
      id2string(replacement_parameter_p->type_variable().get_identifier());

    // the replacement parameter is a viable one, i.e., it comes from an outer
    // class
    PRECONDITION(
      parameter_full_name.substr(0, parameter_full_name.rfind("::"))
        .compare(
          replacement_parameter_full_name.substr(
            0, replacement_parameter_full_name.rfind("::"))) > 0);

    parameter.type_variable_ref().set_identifier(
      replacement_parameter_full_name);
  }
}

/// Recursively find all generic type parameters of a given type and replace
/// their identifiers if matching replacement parameter exist.
/// Example: class `Outer<T>` has an inner class `Inner` that has a field
/// `t` of type `Generic<T>`. This function ensures that the parameter points to
/// `java::Outer::T` instead of `java::Outer$Inner::T`.
static void find_and_replace_parameters(
  typet &type,
  const std::vector<java_generic_parametert> &replacement_parameters)
{
  if(is_java_generic_parameter(type))
  {
    find_and_replace_parameter(
      to_java_generic_parameter(type), replacement_parameters);
  }
  else if(is_java_generic_type(type))
  {
    java_generic_typet &generic_type = to_java_generic_type(type);
    std::vector<reference_typet> &arguments =
      generic_type.generic_type_arguments();
    for(auto &argument : arguments)
    {
      find_and_replace_parameters(argument, replacement_parameters);
    }
  }
  else if(is_java_generic_struct_tag_type(type))
  {
    java_generic_struct_tag_typet &generic_base =
      to_java_generic_struct_tag_type(type);
    std::vector<reference_typet> &gen_types = generic_base.generic_types();
    for(auto &gen_type : gen_types)
    {
      find_and_replace_parameters(gen_type, replacement_parameters);
    }
  }
}

/// Convert parsed annotations into the symbol table
/// \param parsed_annotations: The parsed annotations to convert
/// \param java_annotations: The java_annotationt collection to populate
void convert_annotations(
  const java_bytecode_parse_treet::annotationst &parsed_annotations,
  std::vector<java_annotationt> &java_annotations)
{
  for(const auto &annotation : parsed_annotations)
  {
    java_annotations.emplace_back(annotation.type);
    std::vector<java_annotationt::valuet> &values =
      java_annotations.back().get_values();
    std::transform(
      annotation.element_value_pairs.begin(),
      annotation.element_value_pairs.end(),
      std::back_inserter(values),
      [](const decltype(annotation.element_value_pairs)::value_type &value) {
        return java_annotationt::valuet(value.element_name, value.value);
      });
  }
}

/// Convert java annotations, e.g. as retrieved from the symbol table, back
/// to type annotationt (inverse of convert_annotations())
/// \param java_annotations: The java_annotationt collection to convert
/// \param annotations: The annotationt collection to populate
void convert_java_annotations(
  const std::vector<java_annotationt> &java_annotations,
  java_bytecode_parse_treet::annotationst &annotations)
{
  for(const auto &java_annotation : java_annotations)
  {
    annotations.emplace_back(java_bytecode_parse_treet::annotationt());
    auto &annotation = annotations.back();
    annotation.type = java_annotation.get_type();

    std::transform(
      java_annotation.get_values().begin(),
      java_annotation.get_values().end(),
      std::back_inserter(annotation.element_value_pairs),
      [](const java_annotationt::valuet &value)
        -> java_bytecode_parse_treet::annotationt::element_value_pairt {
          return {value.get_name(), value.get_value()};
        });
  }
}

/// Checks if the class is implicitly generic, i.e., it is an inner class of
/// any generic class. All uses of the implicit generic type parameters within
/// the inner class are updated to point to the type parameters of the
/// corresponding outer classes.
void mark_java_implicitly_generic_class_type(
  const irep_idt &class_name,
  symbol_tablet &symbol_table)
{
  const std::string qualified_class_name = "java::" + id2string(class_name);
  PRECONDITION(symbol_table.has_symbol(qualified_class_name));
  symbolt &class_symbol = symbol_table.get_writeable_ref(qualified_class_name);
  java_class_typet &class_type = to_java_class_type(class_symbol.type);

  // the class must be an inner non-static class, i.e., have a field this$*
  // TODO this should be simplified once static inner classes are marked
  // during parsing
  bool no_this_field = std::none_of(
    class_type.components().begin(),
    class_type.components().end(),
    [](const struct_union_typet::componentt &component)
    {
      return id2string(component.get_name()).substr(0, 5) == "this$";
    });
  if(no_this_field)
  {
    return;
  }

  // create a vector of all generic type parameters of all outer classes, in
  // the order from the outer-most inwards
  std::vector<java_generic_parametert> implicit_generic_type_parameters;
  std::string::size_type outer_class_delimiter =
    qualified_class_name.rfind("$");
  while(outer_class_delimiter != std::string::npos)
  {
    std::string outer_class_name =
      qualified_class_name.substr(0, outer_class_delimiter);
    if(symbol_table.has_symbol(outer_class_name))
    {
      const symbolt &outer_class_symbol =
        symbol_table.lookup_ref(outer_class_name);
      const java_class_typet &outer_class_type =
        to_java_class_type(outer_class_symbol.type);
      if(is_java_generic_class_type(outer_class_type))
      {
        const auto &outer_generic_type_parameters =
          to_java_generic_class_type(outer_class_type).generic_types();
        implicit_generic_type_parameters.insert(
          implicit_generic_type_parameters.begin(),
          outer_generic_type_parameters.begin(),
          outer_generic_type_parameters.end());
      }
      outer_class_delimiter = outer_class_name.rfind("$");
    }
    else
    {
      throw missing_outer_class_symbol_exceptiont(
        outer_class_name, qualified_class_name);
    }
  }

  // if there are any implicit generic type parameters, mark the class
  // implicitly generic and update identifiers of type parameters used in fields
  if(!implicit_generic_type_parameters.empty())
  {
    class_symbol.type = java_implicitly_generic_class_typet(
      class_type, implicit_generic_type_parameters);

    for(auto &field : class_type.components())
    {
      find_and_replace_parameters(
        field.type(), implicit_generic_type_parameters);
    }

    for(auto &base : class_type.bases())
    {
      find_and_replace_parameters(
        base.type(), implicit_generic_type_parameters);
    }
  }
}
