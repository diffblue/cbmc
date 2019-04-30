/*******************************************************************\

Module: XML Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// XML Interface

#ifndef CPROVER_XMLLANG_XML_INTERFACE_H
#define CPROVER_XMLLANG_XML_INTERFACE_H

class cmdlinet;
class message_handlert;

/// Parse XML-formatted commandline options from stdin.
///
/// Example:
/// \code{.xml}
/// <options>
///   <valueOption actual="main.c"/>
///   <valueOption name="function" actual="foo"/>
///   <valueOption name="unwind" actual="3"/>
///   <valueOption name="property" actual="foo.assertion.1"/>
///   <valueOption name="property" actual="foo.assertion.3"/>
///   <flagOption name="trace" actual="on"/>
///   <flagOption name="show-properties" actual="off"/>
/// </options>
/// \endcode
void xml_interface(cmdlinet &, message_handlert &);

// clang-format off
#define OPT_XML_INTERFACE \
  "(xml-ui)" \
  "(xml-interface)"

#define HELP_XML_INTERFACE \
  " --xml-ui                     use XML-formatted output\n" \
  " --xml-interface              bi-directional XML interface\n"
// clang-format on

#endif // CPROVER_XMLLANG_XML_INTERFACE_H
