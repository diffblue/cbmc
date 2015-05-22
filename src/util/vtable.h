#ifndef CPROVER_VTABLE_H_
#define CPROVER_VTABLE_H_

class vtable_namest {
public:
  static const char VT_PTR[];

  static std::string get_type(const std::string &class_name);

  static std::string get_type(const class typet &class_type);

  static std::string get_type(const class exprt &instance);

  static std::string get_table(const std::string &class_name);

  static std::string get_table(const class typet &class_type);

  static std::string get_table(const class exprt &instance);

  static std::string get_table_base(const std::string &class_base_name);

  static std::string get_type_base(const std::string &class_base_name);

  static std::string get_pointer(const std::string &class_name);
};

#endif /* CPROVER_VTABLE_H_ */
