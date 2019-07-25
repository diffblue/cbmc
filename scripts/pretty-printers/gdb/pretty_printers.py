import gdb


# Class for pretty-printing dstringt
class DStringPrettyPrinter:
    "Print a dstringt"

    def __init__(self, val):
        self.val = val

    def to_string(self):
        # ideally, we want to access the memory where the string
        # is stored directly instead of calling a function. However,
        # this is simpler.
        try:
            raw_address = str(self.val.address)

            # If it's ::empty, we know it's empty without going further.
            if "::empty" in raw_address:
                return ""

            # Split the address on the first space, return that value
            # Addresses are usually {address} {optional type_name}
            typed_pointer = "((const {} *){})".format(self.val.type, raw_address.split(None, 1)[0])

            string_no = self.val["no"]

            # Check that the pointer is not null.
            null_ptr = gdb.parse_and_eval("{} == 0".format(typed_pointer))
            if null_ptr.is_optimized_out:
                return "{}: <Ptr optimized out>".format(string_no)
            if null_ptr:
                return ""

            table_len = gdb.parse_and_eval("get_string_container().string_vector.size()")
            if table_len.is_optimized_out:
                return "{}: <Table len optimized out>".format(string_no)
            if string_no >= table_len:
                return "{} index ({}) out of range".format(self.val.type, string_no)

            value = gdb.parse_and_eval("{}->c_str()".format(typed_pointer))
            if value.is_optimized_out:
                return "{}: <Optimized out>".format(string_no)
            return "{}: \"{}\"".format(string_no, value.string().replace("\0", "").replace("\"", "\\\""))
        except:
            return ""

    def display_hint(self):
        return None


class InstructionPrettyPrinter:
    def __init__(self, val):
        self.val = val

    def to_string(self):
        try:
            raw_address = str(self.val.address)
            variable_accessor = "(*({}*){})".format(self.val.type, raw_address.split(None, 1)[0])
            expr = "{0}.to_string()".format(variable_accessor)
            return gdb.parse_and_eval(expr)
        except:
            return ""

    def display_hint(self):
        return "string"


# If you change the name of this make sure to change install.py too.
def load_cbmc_printers():
    printers = gdb.printing.RegexpCollectionPrettyPrinter("CBMC")

    # First argument is the name of the pretty-printer, second is a regex match for which type
    # it should be applied too, third is the class that should be called to pretty-print that type.
    printers.add_printer("dstringt", "^(?:dstringt|irep_idt)", DStringPrettyPrinter)
    printers.add_printer("instructiont", "^goto_programt::instructiont", InstructionPrettyPrinter)
    # We aren't associating with a particular object file, so pass in None instead of gdb.current_objfile()
    gdb.printing.register_pretty_printer(None, printers, replace=True)
