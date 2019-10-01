/*******************************************************************\

Module: Loop analysis

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Data structure representing a loop in a GOTO program and an interface shared
/// by all analyses that find program loops.

#ifndef CPROVER_ANALYSES_LOOP_ANALYSIS_H
#define CPROVER_ANALYSES_LOOP_ANALYSIS_H

template <class P, class T>
class loop_analysist;

/// A loop, specified as a set of instructions
template <class P, class T>
class loop_templatet
{
  typedef loop_analysist<P, T> parent_analysist;
  typedef std::set<T> loop_instructionst;
  loop_instructionst loop_instructions;

  friend loop_analysist<P, T>;

public:
  explicit loop_templatet(parent_analysist &loop_analysis)
    : loop_analysis(loop_analysis)
  {
  }

  template <typename InstructionSet>
  loop_templatet(parent_analysist &loop_analysis, InstructionSet &&instructions)
    : loop_instructions(std::forward<InstructionSet>(instructions)),
      loop_analysis(loop_analysis)
  {
  }

  /// Returns true if \p instruction is in this loop
  bool contains(const T instruction) const
  {
    return loop_analysis.loop_contains(*this, instruction);
  }

  /// Get the \ref parent_analysist analysis this loop relates to
  const parent_analysist &get_loop_analysis() const
  {
    return loop_analysis;
  }
  /// Get the \ref parent_analysist analysis this loop relates to
  parent_analysist &get_loop_analysis()
  {
    return loop_analysis;
  }

  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename loop_instructionst::const_iterator const_iterator;

  /// Iterator over this loop's instructions
  const_iterator begin() const
  {
    return loop_instructions.begin();
  }

  /// Iterator over this loop's instructions
  const_iterator end() const
  {
    return loop_instructions.end();
  }

  /// Number of instructions in this loop
  std::size_t size() const
  {
    return loop_instructions.size();
  }

  /// Returns true if this loop contains no instructions
  bool empty() const
  {
    return loop_instructions.empty();
  }

  /// Adds \p instruction to this loop. The caller must verify that the added
  /// instruction does not alter loop structure; if it does they must discard
  /// and recompute the related \ref parent_analysist instance.
  /// \return true if the instruction is new
  bool insert_instruction(const T instruction)
  {
    return loop_instructions.insert(instruction).second;
  }

private:
  parent_analysist &loop_analysis;
};

template <class P, class T>
class loop_analysist
{
public:
  typedef loop_templatet<P, T> loopt;
  // map loop headers to loops
  typedef std::map<T, loopt> loop_mapt;

  loop_mapt loop_map;

  void output(std::ostream &) const;

  /// Returns true if \p instruction is in \p loop
  bool loop_contains(const loopt &loop, const T instruction) const
  {
    return loop.loop_instructions.count(instruction);
  }

  /// Returns true if \p instruction is the header of any loop
  bool is_loop_header(const T instruction) const
  {
    return loop_map.count(instruction);
  }

  loop_analysist() = default;

  // The loop structures stored in `loop_map` contain back-pointers to this
  // class, so we forbid copying or moving the analysis struct. If this becomes
  // necessary then either add a layer of indirection or update the loop_map
  // back-pointers on copy/move.
  loop_analysist(const loop_analysist &) = delete;
  loop_analysist(loop_analysist &&) = delete;
  loop_analysist &operator=(const loop_analysist &) = delete;
  loop_analysist &operator=(loop_analysist &&) = delete;
};

/// Print all natural loops that were found
template <class P, class T>
void loop_analysist<P, T>::output(std::ostream &out) const
{
  for(const auto &loop : loop_map)
  {
    unsigned n = loop.first->location_number;

    std::unordered_set<std::size_t> backedge_location_numbers;
    for(const auto &backedge : loop.first->incoming_edges)
      backedge_location_numbers.insert(backedge->location_number);

    out << n << " is head of { ";

    std::vector<std::size_t> loop_location_numbers;
    for(const auto &loop_instruction_it : loop.second)
      loop_location_numbers.push_back(loop_instruction_it->location_number);
    std::sort(loop_location_numbers.begin(), loop_location_numbers.end());

    for(const auto location_number : loop_location_numbers)
    {
      if(location_number != loop_location_numbers.at(0))
        out << ", ";
      out << location_number;
      if(backedge_location_numbers.count(location_number))
        out << " (backedge)";
    }
    out << " }\n";
  }
}

template <class LoopAnalysis>
void show_loops(const goto_modelt &goto_model, std::ostream &out)
{
  forall_goto_functions(it, goto_model.goto_functions)
  {
    out << "*** " << it->first << '\n';

    LoopAnalysis loop_analysis;
    loop_analysis(it->second.body);
    loop_analysis.output(out);

    out << '\n';
  }
}

#endif // CPROVER_ANALYSES_LOOP_ANALYSIS_H
