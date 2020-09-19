/*******************************************************************\

Module:

Authors: Murali Talupur, talupur@amazon.com
         Lefan Zhang,    lefanz@amazon.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_RR_ABSTRACTION_SPECT_H
#define CPROVER_GOTO_INSTRUMENT_RR_ABSTRACTION_SPECT_H

#include <limits>
#include <list>
#include <map>
#include <string>
#include <tuple>
#include <vector>

class rr_abstraction_spect
{
public:
  rr_abstraction_spect()
  {
  }
  // This constructor parses the json abstraction
  // specification and populates the class.
  rr_abstraction_spect(std::string, message_handlert &);

  // gathers file names from all the individual specs and returns a list.
  std::vector<std::string> get_abstraction_function_files() const;

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

    struct entityt
    {
      // Name of the array/list being abstracted
      irep_idt
        // Should be in the id format: function::x::name, the unique identifier
        name;
      std::string name_of_abst;

    public:
      entityt()
      {
      }
      explicit entityt(irep_idt _name) : name(_name)
      {
      }
      entityt(const entityt &_entity)
        : name(_entity.name), name_of_abst(_entity.name_of_abst)
      {
      }

      irep_idt entity_name() const
      {
        return name;
      }

      void set_entity_name(const irep_idt &new_name)
      {
        name = new_name;
      }

      std::string entity_abst() const
      {
        return name_of_abst;
      }

      std::string entity_path()
      {
        return ("foo");
      };
    };

  protected:
    // Abstraction func file
    std::string abst_func_file;

    // Arrays to be abstracted
    std::unordered_map<irep_idt, entityt> abst_arrays;

    // Index vars to be abstracted
    std::unordered_map<irep_idt, entityt> abst_indices;

    // Length vars to be abstracted
    std::unordered_map<irep_idt, entityt> abst_lengths;

    // Shape of the abstraction
    abst_shapet shape;

    // Abstraction functions follow.
    // These should be defined in the abst_funcs_file or hard-coded.
    // In abst_funcs_file function will begin with prefixes such as
    // is_precise, compare_indices etc plus some shape identifier.

    // Says if an index into the abstracted entity is precisely tracked or not.
    irep_idt is_precise_func;
    // Says how the two indices into abstracted entity compare.
    irep_idt compare_indices_func;
    // Addition over abstract indices
    irep_idt addition_func;
    // Subtraction over abstract indices
    irep_idt minus_func;
    // Translate a concrete index to an abst index
    irep_idt abstract_func;

    // the index of this spect in the rr_abstraction_spect
    size_t spect_index;

  public:
    spect()
    {
    }
    spect(const spect &_spec)
      : abst_func_file(_spec.abst_func_file),
        abst_arrays(_spec.abst_arrays),
        abst_indices(_spec.abst_indices),
        abst_lengths(_spec.abst_lengths),
        shape(_spec.shape),
        is_precise_func(_spec.is_precise_func),
        compare_indices_func(_spec.compare_indices_func),
        addition_func(_spec.addition_func),
        minus_func(_spec.minus_func),
        abstract_func(_spec.abstract_func),
        spect_index(_spec.spect_index)
    {
    }

    // We will have functions for accessing and modifying the above data.
    // _type: "array", "scalar", "length"
    void insert_entity(const irep_idt &_name, const std::string &_type)
    {
      entityt new_entity(_name);
      if(_type == "array")
        abst_arrays.insert({_name, new_entity});
      else if(_type == "scalar")
        abst_indices.insert({_name, new_entity});
      else if(_type == "length")
      {
        abst_lengths.insert({_name, new_entity});
        abst_indices.insert({_name, new_entity});
      }
      else
        throw "unknown entity type: " + _type;
    }

    const std::unordered_map<irep_idt, entityt> &get_abst_arrays() const
    {
      return abst_arrays;
    }

    const std::unordered_map<irep_idt, entityt> &get_abst_indices() const
    {
      return abst_indices;
    }

    const std::unordered_map<irep_idt, entityt> &get_abst_lengths() const
    {
      return abst_lengths;
    }

    const bool has_entity(const irep_idt &entity_name) const
    {
      return (abst_arrays.find(entity_name) != abst_arrays.end()) ||
             (abst_indices.find(entity_name) != abst_indices.end());
    }

    const bool has_array_entity(const irep_idt &entity_name) const
    {
      return (abst_arrays.find(entity_name) != abst_arrays.end());
    }

    const bool has_index_entity(const irep_idt &entity_name) const
    {
      return (abst_indices.find(entity_name) != abst_indices.end());
    }

    const irep_idt get_length_index_name() const
    {
      return shape.get_length_index_name();
    }

    // set abst func file path
    void set_abst_func_file(const std::string &_abst_func_file)
    {
      abst_func_file = _abst_func_file;
    }

    // get abst func file
    std::string get_abst_func_file() const
    {
      return abst_func_file;
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

    // get addition func
    const irep_idt &get_minus_func() const
    {
      return minus_func;
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

    // get is_precise func
    const irep_idt &get_abstract_func() const
    {
      return abstract_func;
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

    // compare if two spect have the same abst shape
    bool compare_shape(const spect &other) const
    {
      if(abst_arrays.size() != other.abst_arrays.size())
        return false;
      if(abst_indices.size() != other.abst_indices.size())
        return false;
      for(const auto &array : abst_arrays)
        if(other.abst_arrays.find(array.first) == other.abst_arrays.end())
          return false;
      for(const auto &index : abst_indices)
        if(other.abst_indices.find(index.first) == other.abst_indices.end())
          return false;
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
      std::unordered_map<irep_idt, irep_idt> _name_pairs) const;
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
  rr_abstraction_spect update_abst_spec(
    irep_idt old_function,
    irep_idt new_function,
    std::unordered_map<irep_idt, irep_idt> _name_pairs) const;

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

  // compare if two spect have the same structure
  bool compare_shape(const rr_abstraction_spect &other) const
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
  std::string get_entities_string() const;
  // print all entities
  void print_entities() const;

protected:
  std::vector<spect> specs;
  irep_idt function; // function name, no need to have path
};

#endif // CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H
