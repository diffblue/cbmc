/*******************************************************************\

Module: RRA Specification

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_RRA_SPEC_H
#define CPROVER_GOTO_INSTRUMENT_RRA_SPEC_H

#include <limits>
#include <list>
#include <map>
#include <string>
#include <tuple>
#include <vector>

class rra_spect
{
public:
  rra_spect()
  {
  }
  // This constructor parses the json abstraction specification
  // and populates the class.
  rra_spect(std::string, message_handlert &);

  // Gathers file names from all the individual specs and returns a list.
  std::vector<std::string> get_abstraction_function_files() const;

  void generate_abstract_function_files();
  void remove_abstract_function_files();

public:
  struct spect
  {
  public:
    struct abst_shapet
    {
      std::vector<irep_idt> indices;
      std::vector<std::string> assumptions;
      std::string shape_type; // e.g. "*cc*"
    public:
      abst_shapet()
      {
      }
      abst_shapet(
        std::vector<irep_idt> _indices,
        std::vector<std::string> _assumptions,
        std::string _shape_type)
        : indices(_indices), assumptions(_assumptions), shape_type(_shape_type)
      {
      }
      abst_shapet(const abst_shapet &other)
        : indices(other.indices),
          assumptions(other.assumptions),
          shape_type(other.shape_type)
      {
      }
      void add_index(const irep_idt &_index)
      {
        indices.push_back(_index);
      }
      void add_assumption(const std::string &_assumption)
      {
        assumptions.push_back(_assumption);
      }
      void set_shape_type(const std::string &_shape_type)
      {
        shape_type = _shape_type;
      }
      bool operator==(const abst_shapet &other) const
      {
        if(indices.size() != other.indices.size())
          return false;
        if(assumptions.size() != other.assumptions.size())
          return false;
        for(size_t i = 0; i < indices.size(); i++)
          if(indices[i] != other.indices[i])
            return false;
        for(size_t i = 0; i < assumptions.size(); i++)
          if(assumptions[i] != other.assumptions[i])
            return false;
        return (shape_type == other.shape_type);
      }
      static irep_idt
      get_index_name(const irep_idt &raw_name, const size_t &spec_index)
      {
        return irep_idt(
          "$abst$spec" + std::to_string(spec_index) + "$" +
          std::string(raw_name.c_str()));
      }
      const std::vector<irep_idt> &get_indices() const
      {
        return indices;
      }
      const irep_idt get_length_index_name() const
      {
        INVARIANT(
          indices.size() > 0,
          "shape should have at least a length concrete variable");
        return *(indices.end() - 1);
      }
      std::vector<exprt> get_assumption_exprs(
        const namespacet &ns,
        const size_t &spec_index) const;
    };

    struct func_call_arg_namet
    {
      irep_idt
        // Name of the argument in the callee function
        name;
      enum arg_translate_typet
      {
        REGULAR,
        ENTITY_TO_POINTER,
        POINTER_TO_ENTITY
      };
      arg_translate_typet
        // Whether it is a translation between entity and pointer
        type;
      func_call_arg_namet(
        const irep_idt &_name,
        const arg_translate_typet &_type)
        : name(_name), type(_type)
      {
      }
    };

    class entityt
    {
    public:
      enum entityt_type
      {
        ARRAY,
        SCALAR,
        LENGTH,
        STRUCT,
        STRUCT_POINTER,
        CONST_C_STR
      };

      // Name of the entity being abstracted
      irep_idt
        // Should be in the id format: function::x::name, the unique identifier
        name;
      entityt_type
        // Could be "array", "length", "scalar", "struct", "struct_pointer"
        type;
      std::unordered_map<irep_idt, std::unique_ptr<entityt>> sub_entities;

      entityt()
      {
      }
      explicit entityt(irep_idt _name) : name(_name)
      {
      }
      entityt(irep_idt _name, entityt_type _type) : name(_name), type(_type)
      {
      }
      entityt(const entityt &_entity) : name(_entity.name), type(_entity.type)
      {
        sub_entities = std::unordered_map<irep_idt, std::unique_ptr<entityt>>();
        for(const auto &k_v : _entity.sub_entities)
          sub_entities.insert(
            {k_v.first, std::unique_ptr<entityt>(new entityt(*k_v.second))});
      }
      ~entityt()
      {
        for(auto &k_v : sub_entities)
          k_v.second.reset();
      }
      entityt &operator=(const entityt &other)
      {
        name = other.name;
        type = other.type;
        sub_entities = std::unordered_map<irep_idt, std::unique_ptr<entityt>>();
        for(const auto &k_v : other.sub_entities)
          sub_entities.insert(
            {k_v.first, std::unique_ptr<entityt>(new entityt(*k_v.second))});
        return *this;
      }

      irep_idt entity_name() const
      {
        return name;
      }

      void set_entity_name(const irep_idt &new_name)
      {
        name = new_name;
      }

      static bool compare_type(entityt_type type1, entityt_type type2)
      {
        if(
          (type1 == SCALAR && type2 == LENGTH) ||
          (type1 == LENGTH && type2 == SCALAR))
          return true;
        return type1 == type2;
      }
      bool operator==(const entityt &_other) const
      {
        if(name != _other.name || !compare_type(type, _other.type))
          return false;
        if(sub_entities.size() != _other.sub_entities.size())
          return false;
        for(const auto &key_val : sub_entities)
        {
          const irep_idt &key = key_val.first;
          const entityt &val = *key_val.second;
          if(_other.sub_entities.find(key) == _other.sub_entities.end())
            return false;
          if(!(val == *_other.sub_entities.at(key)))
            return false;
        }
        return true;
      }
    };

    class array_entityt : public entityt
    {
    public:
      array_entityt() : entityt()
      {
        type = entityt_type::ARRAY;
      }
      explicit array_entityt(irep_idt _name) : entityt(_name)
      {
        type = entityt_type::ARRAY;
      }
      array_entityt(const array_entityt &_entity) : entityt(_entity)
      {
      }
    };

    class scalar_entityt : public entityt
    {
    public:
      scalar_entityt() : entityt()
      {
        type = entityt_type::SCALAR;
      }
      explicit scalar_entityt(irep_idt _name) : entityt(_name)
      {
        type = entityt_type::SCALAR;
      }
      scalar_entityt(const scalar_entityt &_entity) : entityt(_entity)
      {
      }
    };

    class length_entityt : public entityt
    {
    public:
      length_entityt() : entityt()
      {
        type = entityt_type::LENGTH;
      }
      explicit length_entityt(irep_idt _name) : entityt(_name)
      {
        type = entityt_type::LENGTH;
      }
      length_entityt(const length_entityt &_entity) : entityt(_entity)
      {
      }
    };

    class struct_entityt : public entityt
    {
    public:
      struct_entityt() : entityt()
      {
        type = entityt_type::STRUCT;
      }
      explicit struct_entityt(irep_idt _name) : entityt(_name)
      {
        type = entityt_type::STRUCT;
      }
      struct_entityt(const struct_entityt &_entity) : entityt(_entity)
      {
      }
    };

    class struct_pointer_entityt : public entityt
    {
    public:
      struct_pointer_entityt() : entityt()
      {
        type = entityt_type::STRUCT_POINTER;
      }
      explicit struct_pointer_entityt(irep_idt _name) : entityt(_name)
      {
        type = entityt_type::STRUCT_POINTER;
      }
      struct_pointer_entityt(const struct_pointer_entityt &_entity)
        : entityt(_entity)
      {
      }
    };

    array_entityt &to_array_entity(entityt &entity)
    {
      PRECONDITION(entity.type == entityt::entityt_type::ARRAY);
      return static_cast<array_entityt &>(entity);
    }

    const array_entityt &to_array_entity(const entityt &entity)
    {
      PRECONDITION(entity.type == entityt::entityt_type::ARRAY);
      return static_cast<const array_entityt &>(entity);
    }

    scalar_entityt &to_scalar_entity(entityt &entity)
    {
      PRECONDITION(entity.type == entityt::entityt_type::SCALAR);
      return static_cast<scalar_entityt &>(entity);
    }

    const scalar_entityt &to_scalar_entity(const entityt &entity)
    {
      PRECONDITION(entity.type == entityt::entityt_type::SCALAR);
      return static_cast<const scalar_entityt &>(entity);
    }

    length_entityt &to_length_entity(entityt &entity)
    {
      PRECONDITION(entity.type == entityt::entityt_type::LENGTH);
      return static_cast<length_entityt &>(entity);
    }

    const length_entityt &to_length_entity(const entityt &entity)
    {
      PRECONDITION(entity.type == entityt::entityt_type::LENGTH);
      return static_cast<const length_entityt &>(entity);
    }

  protected:
    // Entities to be abstracted
    std::unordered_map<irep_idt, std::unique_ptr<entityt>> abst_entities;

    // Shape of the abstraction
    abst_shapet shape;

    // Abstraction functions follow.
    // These should be defined in the abstraction_funcs_file or
    // they are hard-coded ones.
    // In abstraction_funcs_file function will begin with prefixes such as
    // is_precise, compare_indices,... followed by the some shape identifier.

    // Says if an index into the abstracted entity is precisely tracked or not.
    irep_idt is_precise_func;
    // Says how the two indices into abstracted entity compare.
    irep_idt compare_indices_func;
    // Addition over abstract indices
    irep_idt addition_func;
    // Subtraction over abstract indices
    irep_idt minus_func;
    // Multiply abstract indices with concrete num
    irep_idt multiply_func;
    // Translate a concrete index to an abst index
    irep_idt abstract_func;
    // Translate a abst index to a concrete index
    irep_idt concretize_func;

    // the index of this spect in the rra_spect
    size_t spect_index;

    // search for all entities within ent
    static std::unordered_map<irep_idt, entityt>
    get_all_entities(const entityt &ent, const irep_idt &prefix);

    // search for all entities within ent with type "type"
    static std::unordered_map<irep_idt, entityt> search_for_entities(
      const entityt &ent,
      const entityt::entityt_type &type,
      const irep_idt &prefix);

  public:
    spect()
    {
    }
    spect(const spect &_spec)
      : shape(_spec.shape),
        is_precise_func(_spec.is_precise_func),
        compare_indices_func(_spec.compare_indices_func),
        addition_func(_spec.addition_func),
        minus_func(_spec.minus_func),
        multiply_func(_spec.multiply_func),
        abstract_func(_spec.abstract_func),
        concretize_func(_spec.concretize_func),
        spect_index(_spec.spect_index)
    {
      abst_entities = std::unordered_map<irep_idt, std::unique_ptr<entityt>>();
      for(const auto &k_v : _spec.abst_entities)
        abst_entities.insert(
          {k_v.first, std::unique_ptr<entityt>(new entityt(*k_v.second))});
    }

    spect &operator=(const spect &other)
    {
      shape = other.shape;
      is_precise_func = other.is_precise_func;
      compare_indices_func = other.compare_indices_func;
      addition_func = other.addition_func;
      minus_func = other.minus_func;
      multiply_func = other.multiply_func;
      abstract_func = other.abstract_func;
      concretize_func = other.concretize_func;
      spect_index = other.spect_index;
      abst_entities = std::unordered_map<irep_idt, std::unique_ptr<entityt>>();
      for(const auto &k_v : other.abst_entities)
        abst_entities.insert(
          {k_v.first, std::unique_ptr<entityt>(new entityt(*k_v.second))});
      return *this;
    }

    ~spect()
    {
      for(auto &k_v : abst_entities)
        k_v.second.reset();
    }

    // Insert an entity
    // The name should be complete "xxx->xxx.xxx"
    // "entity" is the entity itself
    void insert_entity(const irep_idt &_name, const entityt &entity);

    // We will have functions for accessing and modifying the above data.
    // _type: "ARRAY", "SCALAR", "LENGTH", etc.
    void
    insert_entity(const irep_idt &_name, const entityt::entityt_type &_type);

    // We will have functions for accessing and modifying the above data.
    // _type: "array", "scalar", "length", etc.
    void insert_entity(const irep_idt &_name, const std::string &_type);

    // Return the top level entities, which are "roots" in the entity forest
    std::unordered_map<irep_idt, entityt> get_top_level_entities() const;

    // Return all nodes in the entity forest
    std::unordered_map<irep_idt, entityt> get_all_abst_entities() const;

    // Return all nodes with type "ARRAY" in the entity forest
    std::unordered_map<irep_idt, entityt> get_abst_arrays() const;

    // Return all nodes with type "CONST_C_STR" in the entity forest
    std::unordered_map<irep_idt, entityt> get_abst_const_c_strs() const;

    // Return all nodes with type "SCALAR" or "LENGTH" in the entity forest
    std::unordered_map<irep_idt, entityt> get_abst_indices() const;

    // Return all nodes with type "LENGTH" in the entity forest
    std::unordered_map<irep_idt, entityt> get_abst_lengths() const;

    static void search_all_lengths_and_generate_path(
      std::vector<entityt> &current_path,
      std::vector<std::vector<entityt>> &results);

    // find all length variables' top level entities' name (the symbol)
    // together with the length variables' exprt
    // e.g. if buf.len is a length variable,
    // ("buf", exprt<buf.len>) will be returned as a pair
    std::vector<std::pair<irep_idt, exprt>>
    get_abst_lengths_with_expr(const namespacet &ns) const;

    const bool has_entity(const irep_idt &entity_name) const
    {
      auto all_abst_entities = get_all_abst_entities();
      return all_abst_entities.find(entity_name) != all_abst_entities.end();
    }

    const bool has_array_entity(const irep_idt &entity_name) const
    {
      const auto abst_arrays = get_abst_arrays();
      return (abst_arrays.find(entity_name) != abst_arrays.end());
    }

    const bool has_const_c_str_entity(const irep_idt &entity_name) const
    {
      const auto abst_c_strs = get_abst_const_c_strs();
      return (abst_c_strs.find(entity_name) != abst_c_strs.end());
    }

    const bool has_index_entity(const irep_idt &entity_name) const
    {
      const auto abst_indices = get_abst_indices();
      return (abst_indices.find(entity_name) != abst_indices.end());
    }

    const irep_idt get_length_index_name() const
    {
      return shape.get_length_index_name();
    }

    // set addition func
    void set_addition_func(const irep_idt &_func_name)
    {
      addition_func = _func_name;
    }

    // get addition func
    const irep_idt &get_addition_func() const
    {
      return addition_func;
    }

    // set minus func
    void set_minus_func(const irep_idt &_func_name)
    {
      minus_func = _func_name;
    }

    // get minus func
    const irep_idt &get_minus_func() const
    {
      return minus_func;
    }

    // set multiply func
    void set_multiply_func(const irep_idt &_func_name)
    {
      multiply_func = _func_name;
    }

    // get multiply func
    const irep_idt &get_multiply_func() const
    {
      return multiply_func;
    }

    // set is_precise func
    void set_precise_func(const irep_idt &_func_name)
    {
      is_precise_func = _func_name;
    }

    // get is_precise func
    const irep_idt &get_precise_func() const
    {
      return is_precise_func;
    }

    // set abstract_func
    void set_abstract_func(const irep_idt &_func_name)
    {
      abstract_func = _func_name;
    }

    // get abstract_func
    const irep_idt &get_abstract_func() const
    {
      return abstract_func;
    }

    // get concretize func
    void set_concretize_func(const irep_idt &_func_name)
    {
      concretize_func = _func_name;
    }

    // get concretize func
    const irep_idt &get_concretize_func() const
    {
      return concretize_func;
    }

    // set the shape
    void set_shape(
      const std::vector<irep_idt> &indices,
      const std::vector<std::string> &assumptions,
      const std::string &shape_type)
    {
      std::vector<irep_idt> new_indices(indices);
      for(auto &index : new_indices)
        index = abst_shapet::get_index_name(index, spect_index);
      shape = abst_shapet(new_indices, assumptions, shape_type);
    }

    std::vector<exprt> get_assumption_exprs(const namespacet &ns) const;

    // compare if two spect have the same abst shape, same entities
    bool compare_shape(const spect &other) const
    {
      if(abst_entities.size() != other.abst_entities.size())
        return false;
      for(const auto &key_val : abst_entities)
      {
        const irep_idt &key = key_val.first;
        const auto &val = key_val.second;
        if(other.abst_entities.find(key) == other.abst_entities.end())
          return false;
        if(!(*val == *other.abst_entities.at(key)))
          return false;
      }

      return shape == other.shape;
    }

    bool compare_shape_only(const spect &other) const
    {
      return shape == other.shape;
    }

    const std::vector<irep_idt> &get_shape_indices() const
    {
      return shape.get_indices();
    }

    void set_spect_index(const size_t &_index)
    {
      spect_index = _index;
    }
    const size_t &get_spect_index() const
    {
      return spect_index;
    }
    const std::string &get_shape_type() const
    {
      return shape.shape_type;
    }
    // We need to update the abstracted array/list/var names as we cross
    // the function boundary.
    // For example, if function Foo has two arrays f1 and f2
    // that are abstracted.
    // Function Bar is defined as void Bar(array b1, array b2) and
    // suppose Foo calls Bar(f1,f2).
    // Abst_spec in Foo will contain f1, f2. These should be renamed to
    // b1, b2 to obtain abst_spec for Bar.
    // The argument for the following function would be Foo, Bar,
    // {f1: b1, f2: b2}
    // Return a new spect reflecting the changes
    spect update_abst_spec(
      irep_idt old_function,
      irep_idt new_function,
      std::unordered_map<irep_idt, func_call_arg_namet> _name_pairs) const;
  };

  // gather specs
  std::vector<spect> &get_specs()
  {
    return specs;
  }

  // gather specs constant version
  const std::vector<spect> &get_specs() const
  {
    return specs;
  }

  // get function name
  const irep_idt &get_func_name() const
  {
    return function;
  }

  // update all specs when crossing the function call boundary
  rra_spect update_abst_spec(
    irep_idt old_function,
    irep_idt new_function,
    std::unordered_map<irep_idt, spect::func_call_arg_namet> _name_pairs) const;

  // check if a variable is abstracted
  bool has_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec : specs)
    {
      if(spec.has_entity(entity_name))
        return true;
    }
    return false;
  }

  bool has_array_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec : specs)
    {
      if(spec.has_array_entity(entity_name))
        return true;
    }
    return false;
  }

  bool has_const_c_str_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec : specs)
    {
      if(spec.has_const_c_str_entity(entity_name))
        return true;
    }
    return false;
  }

  // check if a variable is an index to be abstracted
  bool has_index_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec : specs)
    {
      if(spec.has_index_entity(entity_name))
        return true;
    }
    return false;
  }

  // return the spect that has the entity,
  // should always run has_index_entity before running this function
  const spect &get_spec_for_index_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec : specs)
    {
      if(spec.has_index_entity(entity_name))
        return spec;
    }
    throw "entity " + std::string(entity_name.c_str()) + " not found";
  }

  // return the spect that has the entity,
  // should always run has_array_entity before running this function
  const spect &get_spec_for_array_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec : specs)
    {
      if(spec.has_array_entity(entity_name))
        return spec;
    }
    throw "entity " + std::string(entity_name.c_str()) + " not found";
  }

  // return the spect that has the entity,
  // should always run has_const_c_str_entity before running this function
  const spect &
  get_spec_for_const_c_str_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec : specs)
    {
      if(spec.has_const_c_str_entity(entity_name))
        return spec;
    }
    throw "entity " + std::string(entity_name.c_str()) + " not found";
  }

  // compare if two spect have the same structure
  bool compare_shape(const rra_spect &other) const
  {
    // In the update_abst_spec function, the result and the
    // original one should have the same spects in terms
    // of both order and shape
    if(specs.size() != other.specs.size())
      return false;
    for(size_t i = 0; i < specs.size(); i++)
      if(!specs[i].compare_shape(other.specs[i]))
        return false;
    return true;
  }

  // get a string containing all entity names
  void get_entities_string(std::ostream &output) const;
  // print all entities
  void print_entities() const;

protected:
  std::vector<spect> specs;
  irep_idt function; // function name, no need to have path
  std::string abst_function_file;
};

#endif // CPROVER_GOTO_INSTRUMENT_RRA_SPEC_H
