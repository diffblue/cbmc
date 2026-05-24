#include <algorithm>
#include <functional>
#include <set>
/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifdef DEBUG
#endif

#include <util/message.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

void cpp_typecheckt::typecheck_method_bodies()
{
  instantiation_stackt old_instantiation_stack;
  old_instantiation_stack.swap(instantiation_stack);

  while(!method_bodies.empty())
  {
    // Dangerous not to take a copy here. We'll have to make sure that
    // convert is never called with the same symbol twice.
    method_bodyt &method_body = *method_bodies.begin();
    symbolt &method_symbol = *method_body.method_symbol;

    template_map.swap(method_body.template_map);
    instantiation_stack.swap(method_body.instantiation_stack);

    method_bodies.erase(method_bodies.begin());

    // Per [temp.variadic]/5: set pack_size_map for empty
    // variadic function template parameters.
    {
      const irept &c_tmpl = method_symbol.type.find(ID_C_template);
      if(c_tmpl.is_not_nil())
      {
        for(const auto &p :
            static_cast<const template_typet &>(c_tmpl).template_parameters())
        {
          if(p.get_bool(ID_ellipsis))
          {
            irep_idt pid = p.type().get(ID_identifier);
            if(
              !pid.empty() &&
              template_map.type_map.find(pid) == template_map.type_map.end())
              template_map.pack_size_map[pid] = 0;
          }
        }
      }
    }

    exprt &body=method_symbol.value;
    if(body.id() == ID_cpp_not_typechecked)
      continue;

    // Per [temp.inst]/1: restore function template map if this
    // is an instantiated member function template.
    if(method_symbol.type.find(irep_idt{"#fn_template_type"}).is_not_nil())
    {
      template_map.build(
        static_cast<const template_typet &>(
          method_symbol.type.find(irep_idt{"#fn_template_type"})),
        static_cast<const cpp_template_args_tct &>(
          method_symbol.type.find(irep_idt{"#fn_template_args"})));
    }

    // Per [temp.variadic]/7: substitute non-empty pack parameter
    // names in the body with their actual types.
    if(!template_map.pack_args_map.empty())
    {
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        if(pa.second.empty())
          continue;
        const std::string full = id2string(pa.first);
        auto p = full.rfind("::");
        const std::string sn =
          p != std::string::npos ? full.substr(p + 2) : full;
        const typet &t = pa.second.front();
        if(t.id() == ID_struct_tag)
        {
          // Use the full struct_tag identifier; resolve_scope can find
          // it directly via id_map / symbol_table.  Naive string-based
          // stripping breaks for nested template types.
          pack_subst[sn] = to_struct_tag_type(t).get_identifier();
        }
      }
      if(!pack_subst.empty())
      {
        std::function<void(irept &)> subst = [&](irept &node)
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
            node.set(
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          node.remove(ID_ellipsis);
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        subst(static_cast<irept &>(body));
      }
    }

    // Per [temp.variadic]/7: substitute non-empty pack parameter
    // names in the body with their actual types.
    if(!template_map.pack_args_map.empty())
    {
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        if(pa.second.empty())
          continue;
        const std::string full = id2string(pa.first);
        auto p = full.rfind("::");
        const std::string sn =
          p != std::string::npos ? full.substr(p + 2) : full;
        const typet &t = pa.second.front();
        if(t.id() == ID_struct_tag)
        {
          std::string tag = id2string(to_struct_tag_type(t).get_identifier());
          if(tag.substr(0, 4) == "tag-")
            tag = tag.substr(4);
          pack_subst[sn] = tag;
        }
      }
      if(!pack_subst.empty())
      {
        std::function<void(irept &)> subst = [&](irept &node)
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
            node.set(
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        subst(static_cast<irept &>(body));
      }
    }

    // Per [temp.variadic]/7: remove empty pack expansion
    // expressions from member initializers in the body.
    if(!template_map.pack_size_map.empty())
    {
      std::set<std::string> ep_names;
      for(const auto &ps : template_map.pack_size_map)
        if(ps.second == 0)
        {
          const std::string f = id2string(ps.first);
          auto p = f.rfind("::");
          ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
        }
      if(!ep_names.empty())
      {
        std::function<bool(const irept &)> has_ep = [&](const irept &n) -> bool
        {
          if(n.id() == ID_template_parameter_symbol_type)
          {
            const std::string f = id2string(n.get(ID_identifier));
            auto p = f.rfind("::");
            if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
              return true;
          }
          if(
            n.id() == ID_name &&
            ep_names.count(id2string(n.get(ID_identifier))))
            return true;
          for(const auto &s : n.get_sub())
            if(has_ep(s))
              return true;
          for(const auto &ns : n.get_named_sub())
            if(has_ep(ns.second))
              return true;
          return false;
        };
        // Check member_initializers in the declarator (if present)
        irept &mi = method_symbol.value.add(ID_member_initializers);
        if(mi.is_not_nil())
        {
          for(auto &init : mi.get_sub())
          {
            auto &subs = init.get_sub();
            subs.erase(
              std::remove_if(
                subs.begin(),
                subs.end(),
                [&](const irept &s) { return has_ep(s); }),
              subs.end());
          }
        }
      }
    }

#ifdef DEBUG
    std::cout << "convert_method_body: " << method_symbol.name << '\n';
    std::cout << "  is_not_nil: " << body.is_not_nil() << '\n';
    std::cout << "  !is_zero: " << (!body.is_zero()) << '\n';
#endif
    if(body.is_not_nil() && body != 0)
    {
      // For template-instantiated methods and methods from system
      // headers, suppress error messages so that failures (e.g.,
      // unsupported standard library constructs) do not increment
      // the error count.
      bool suppress = !instantiation_stack.empty();
      if(!suppress)
      {
        const auto &loc = method_symbol.location;
        const std::string file = id2string(loc.get_file());
        // Only suppress for system headers (paths under /usr/include,
        // /usr/lib, etc.), not for all absolute paths.
        suppress = file.find("/include/") != std::string::npos ||
                   file.find("\\include\\") != std::string::npos ||
                   file.find("/usr/lib/") == 0 ||
                   file.find("/Applications/") == 0;
      }
      if(suppress)
      {
        // Save/restore error count instead of using null_handler.
        // The null_message_handlert causes template instantiations
        // inside the body to fail (e.g., _Deallocate<_New_alignof>)
        // because some code paths behave differently when the
        // message handler is null.
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        suppress_elaborate = false;
        try
        {
          convert_function(method_symbol);
        }
        catch(...)
        {
          // Type-checking failed — clear the partially-checked body
          // so the function is cleanly in the "no body" state.
          method_symbol.value.make_nil();
        }
        get_message_handler().set_message_count(
          messaget::M_ERROR, errors_before);
      }
      else
      {
        had_template_instantiation = false;
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        suppress_elaborate = false;
        try
        {
          convert_function(method_symbol);

          // C++14: update struct component type after auto return type
          // deduction.
          if(
            method_symbol.type.id() == ID_code &&
            has_auto(to_code_type(method_symbol.type).return_type()) == false)
          {
            const irep_idt &class_id = method_symbol.type.get(ID_C_member_name);
            if(!class_id.empty())
            {
              symbolt *class_sym = symbol_table.get_writeable(class_id);
              if(class_sym != nullptr)
              {
                struct_union_typet &struct_type =
                  to_struct_union_type(class_sym->type);
                for(auto &comp : struct_type.components())
                {
                  if(
                    comp.get_name() == method_symbol.name &&
                    comp.type().id() == ID_code &&
                    has_auto(to_code_type(comp.type()).return_type()))
                  {
                    to_code_type(comp.type()).return_type() =
                      to_code_type(method_symbol.type).return_type();
                    break;
                  }
                }
              }
            }
          }
        }
        catch(int)
        {
          // If the error originated from template instantiation
          // (e.g., unsupported STL constructs), suppress it rather
          // than failing the entire translation unit.
          if(had_template_instantiation)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            continue;
          }
          throw;
        }
      }
    }
  }

  // Process remaining deferred method bodies. Some deferred methods
  // were triggered on-demand during the loop above; others were never
  // referenced. We must still process them all because method body
  // type-checking has side effects: it triggers elaboration of
  // referenced classes (e.g., std::bad_alloc), creates parameter
  // symbols, and may add further methods to the queue.
  while(!deferred_method_bodies.empty())
  {
    auto it = deferred_method_bodies.begin();
    method_bodies.push_back(std::move(it->second));
    deferred_method_bodies.erase(it);
  }

  // Process any methods that were just moved from deferred,
  // plus any new methods added as side effects.
  while(!method_bodies.empty())
  {
    method_bodyt &method_body = *method_bodies.begin();
    symbolt &method_symbol = *method_body.method_symbol;

    template_map.swap(method_body.template_map);
    instantiation_stack.swap(method_body.instantiation_stack);

    method_bodies.erase(method_bodies.begin());

    // Per [temp.variadic]/5: set pack_size_map for empty
    // variadic function template parameters.
    {
      const irept &c_tmpl = method_symbol.type.find(ID_C_template);
      if(c_tmpl.is_not_nil())
      {
        for(const auto &p :
            static_cast<const template_typet &>(c_tmpl).template_parameters())
        {
          if(p.get_bool(ID_ellipsis))
          {
            irep_idt pid = p.type().get(ID_identifier);
            if(
              !pid.empty() &&
              template_map.type_map.find(pid) == template_map.type_map.end())
              template_map.pack_size_map[pid] = 0;
          }
        }
      }
    }

    exprt &body = method_symbol.value;
    if(body.id() == ID_cpp_not_typechecked)
      continue;

    if(body.is_not_nil() && body != 0)
    {
      const std::size_t errors_before =
        get_message_handler().get_message_count(messaget::M_ERROR);
      try
      {
        convert_function(method_symbol);
      }
      catch(...)
      {
      }
      get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
    }
  }

  old_instantiation_stack.swap(instantiation_stack);
}

void cpp_typecheckt::add_method_body(symbolt *_method_symbol)
{
#ifdef DEBUG
  std::cout << "add_method_body: " << _method_symbol->name << '\n';
#endif
  // Converting a method body might add method bodies for methods that we have
  // already analyzed. Adding the same method more than once causes duplicated
  // symbol prefixes, therefore we have to keep track.
  if(methods_seen.insert(_method_symbol->name).second)
  {
    // If this method was deferred (its class is a template instance and
    // the method body wasn't type-checked during class instantiation),
    // the current template_map may not contain the class template
    // parameters. Build them from the class symbol so that names like
    // _Alloc inside the method body resolve correctly.
    template_mapt method_map = template_map;
    {
      const irep_idt &class_id = _method_symbol->type.get(ID_C_member_name);
      if(!class_id.empty())
      {
        const symbolt *class_sym = symbol_table.lookup(class_id);
        if(
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template).is_not_nil() &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil())
        {
          method_map.build(
            static_cast<const template_typet &>(
              class_sym->type.find(ID_C_template)),
            static_cast<const cpp_template_args_tct &>(
              class_sym->type.find(ID_C_template_arguments)));
        }
      }
    }
    bool defer = false;
    {
      const irep_idt &class_id = _method_symbol->type.get(ID_C_member_name);
      if(!class_id.empty())
      {
        const symbolt *class_sym = symbol_table.lookup(class_id);
        bool is_template_instance =
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil();
        if(is_template_instance)
        {
          const auto &return_type =
            to_code_type(_method_symbol->type).return_type();
          bool is_ctor = return_type.id() == ID_constructor;
          bool is_dtor = return_type.id() == ID_destructor;
          bool is_virtual = _method_symbol->type.get_bool(ID_C_is_virtual);
          bool is_operator =
            id2string(_method_symbol->base_name).find("operator") !=
            std::string::npos;
          if(!is_ctor && !is_dtor && !is_virtual && !is_operator)
            defer = true;
        }
      }
    }

    if(defer)
    {
      deferred_method_bodies.emplace(
        _method_symbol->name,
        method_bodyt(_method_symbol, method_map, instantiation_stack));
    }
    else
    {
      method_bodies.push_back(
        method_bodyt(_method_symbol, method_map, instantiation_stack));
    }
  }
#ifdef DEBUG
  else
    std::cout << "  already exists\n";
#endif
}
