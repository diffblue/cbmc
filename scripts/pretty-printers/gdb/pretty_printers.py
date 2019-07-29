import gdb


def deconstruct_dstring(val):
    # ideally, we want to access the memory where the string
    # is stored directly instead of calling a function. However,
    # this is simpler.
    try:
        raw_address = str(val.address)

        # If it's ::empty, we know it's empty without going further.
        if "::empty" in raw_address:
            return -1, ""

        # Split the address on the first space, return that value
        # Addresses are usually {address} {optional type_name}
        typed_pointer = "((const {} *){})".format(val.type, raw_address.split(None, 1)[0])

        string_no = val["no"]

        # Check that the pointer is not null.
        null_ptr = gdb.parse_and_eval("{} == 0".format(typed_pointer))
        if null_ptr.is_optimized_out:
            return -1, "{}: <Ptr optimized out>".format(string_no)
        if null_ptr:
            return -1, ""

        table_len = gdb.parse_and_eval("get_string_container().string_vector.size()")
        if table_len.is_optimized_out:
            return -1, "{}: <Table len optimized out>".format(string_no)
        if string_no >= table_len:
            return -1, "{} index ({}) out of range".format(val.type, string_no)

        value = gdb.parse_and_eval("{}->c_str()".format(typed_pointer))
        if value.is_optimized_out:
            return -1, "{}: <Optimized out>".format(string_no)
        return string_no, value.string().replace("\0", "")
    except:
        return -1, ""

# Class for pretty-printing dstringt
class DStringPrettyPrinter:
    "Print a dstringt"

    def __init__(self, val):
        self.val = val

    def to_string(self):
        string_no, value = deconstruct_dstring(self.val)
        if string_no == -1:
            return value
        return "{}: \"{}\"".format(string_no, value.replace("\"", "\\\""))

    def display_hint(self):
        return None


def find_type(type, name):
    type = type.strip_typedefs()
    while True:
        # Strip cv-qualifiers.
        search = "%s::%s" % (type.unqualified(), name)
        try:
            return gdb.lookup_type(search)
        except RuntimeError:
            pass
        # The type was not found, so try the superclass.
        # We only need to check the first superclass.
        type = type.fields()[0].type


class IrepPrettyPrinter:
    "Print an irept"

    def __init__(self, val):
        self.val = val["data"].referenced_value()

    def to_string(self):
        try:
            return "\"{}\"".format(deconstruct_dstring(self.val["data"])[1].replace("\"", "\\\""))
        except:
            return "Exception pretty printing irept"

    def children(self):
        sub = self.val["sub"]
        count = 0
        item = sub["_M_impl"]["_M_start"]
        finish = sub["_M_impl"]["_M_finish"]
        while item != finish:
            yield "sub %d key" % count, "sub[%d]" % count
            yield "sub %d value" % count, item.dereference()
            count += 1
            item += 1

        named_sub = self.val["named_sub"]
        size = named_sub["_M_t"]["_M_impl"]["_M_node_count"]
        node = named_sub["_M_t"]["_M_impl"]["_M_header"]["_M_left"]
        count = 0
        while count != size:
            rep_type = find_type(named_sub.type, "_Rep_type")
            link_type = find_type(rep_type, "_Link_type")
            node_type = link_type.strip_typedefs()
            current = node.cast(node_type).dereference()
            addr_type = current.type.template_argument(0).pointer()
            result = current["_M_storage"]["_M_storage"].address.cast(addr_type).dereference()
            yield "named_sub %d key" % count, "named_sub[\"%s\"]" % deconstruct_dstring(result["first"])[1].replace("\"", "\\\"")
            yield "named_sub %d value" % count, result["second"]
            count += 1
            if count < size:
                # Get the next node
                right = node.dereference()["_M_right"]
                if right:
                    node = right
                    while True:
                        left = node.dereference()["_M_left"]
                        if not left:
                            break
                        node = left
                else:
                    parent = node.dereference()["_M_parent"]
                    while node == parent.dereference()["_M_right"]:
                        node = parent
                        parent = parent.dereference()["_M_parent"]
                    # Not sure what this checks
                    if node.dereference()["_M_right"] != parent:
                        node = parent

    def display_hint(self):
        return "map"


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
