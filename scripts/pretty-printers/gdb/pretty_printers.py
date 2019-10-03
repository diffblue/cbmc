import json
import os
from json import JSONDecodeError

import gdb

script_directory = os.path.dirname(os.path.abspath(__file__))

options_path = os.path.join(script_directory, "options.json")
pretty_printer_options = {}
try:
    with open(os.path.join(script_directory, "options.json"), "r") as json_file:
        pretty_printer_options = json.load(json_file)
except JSONDecodeError as e:
    print("Options file at {0} failed to load. Exception: {1}".format(options_path, e.msg))
except Exception as e:
    print("Error attempting to load configuration. Exception: {1}".format(options_path, e))


def get_option(value):
    return pretty_printer_options.get(value, None)


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


def has_children_nodes(data_ref):
    """ Does this irept have any children. """
    has_subs = data_ref["sub"]["_M_impl"]["_M_start"] != data_ref["sub"]["_M_impl"]["_M_finish"]
    has_named_subs = data_ref["named_sub"]["_M_t"]["_M_impl"]["_M_node_count"] > 0
    return has_subs or has_named_subs


def get_node_value(data_ref):
    """ If the item has children, wrap it in [...]. """
    has_children = has_children_nodes(data_ref)
    id_value = get_id(data_ref)
    if id_value:
        if has_children:
            return "[{0}]".format(id_value)
    elif has_children:
        return "[...]"

    return None


def get_id(data_ref):
    """ Return the ID of a node as a string. """
    _, nested_value = deconstruct_dstring(data_ref["data"])
    if nested_value:
        return nested_value.replace("\"", "\\\"")

    return ""


def untypedef(type_obj):
    """ Strip type definitions off type if required. """
    if (type_obj.code == gdb.TYPE_CODE_REF or
            type_obj.code == getattr(gdb, 'TYPE_CODE_RVALUE_REF', None)):

        type_obj = type_obj.target()

    if type_obj.code == gdb.TYPE_CODE_TYPEDEF:
        type_obj = type_obj.strip_typedefs()

    return type_obj


class DStringPrettyPrinter:
    """Class for printing a dstringt"""

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
    """
    Print an irept. Has two modes.

    CLion mode: prints like a vector, with each elements IDE-shown index
    being the name of a named-sub, or the actual index of a normal sub.

    GDB mode: prints like a map, and just prints key/value pairs of both sub
    and named sub.
    """

    def __init__(self, val):
        self.val = val["data"].referenced_value()
        self.clion_representation = get_option("clion_pretty_printers")

    def to_string(self):
        try:
            return "\"{}\"".format(get_id(self.val))
        except:
            return "Exception pretty printing irept"

    def children(self):
        """ Method that tells GDB what children this object has. """

        # Every node should show their ID. Without this the root node
        # misses any identifier information even if every other child
        # has [...] to tell you what type it is.
        if has_children_nodes(self.val):
            if self.clion_representation:
                yield "ID", self.val["data"]
            else:
                yield "ID key", "ID"
                yield "ID value", self.val["data"]

        # Loop through our subs, print out the index as the key.
        sub = self.val["sub"]
        sub_count = 0
        item = sub["_M_impl"]["_M_start"]
        finish = sub["_M_impl"]["_M_finish"]
        while item != finish:

            node_key = "{}".format(sub_count)
            iter_item = item.dereference()

            # In CLion mode we're considered a vector, which takes one return tuple
            # of (key, value). In map mode, it expects two return tuples,
            # (key identifier, key) and (value identifier, value).
            if self.clion_representation:
                item_deref = iter_item["data"].referenced_value()
                nested_id = get_node_value(iter_item["data"].referenced_value())
                if nested_id:
                    node_key = "{0} {1}".format(node_key, nested_id)
                else:
                    iter_item = item_deref["data"]

                yield node_key, iter_item
            else:
                yield "sub %d key" % sub_count, node_key
                yield "sub %d value" % sub_count, item.dereference()

            sub_count += 1
            item += 1

        # Loop through our named subs, using the sub name as the key.
        named_sub = self.val["named_sub"]
        size = named_sub["_M_t"]["_M_impl"]["_M_node_count"]
        node = named_sub["_M_t"]["_M_impl"]["_M_header"]["_M_left"]
        named_sub_count = 0
        while named_sub_count != size:

            # Wind our way through structure internals to get the data.
            rep_type = find_type(named_sub.type, "_Rep_type")
            link_type = find_type(rep_type, "_Link_type")
            node_type = link_type.strip_typedefs()
            current = node.cast(node_type).dereference()
            addr_type = current.type.template_argument(0).pointer()
            result = current["_M_storage"]["_M_storage"].address.cast(addr_type).dereference()

            # Get the name of the named_sub.
            _, sub_name = deconstruct_dstring(result["first"])
            node_key = sub_name.replace("\"", "\\\"")

            # Print out {name} {value}
            iter_item = result["second"]
            if self.clion_representation:
                item_deref = iter_item["data"].referenced_value()
                nested_id = get_node_value(item_deref)
                if nested_id:
                    node_key = "{0} {1}".format(node_key, nested_id)
                else:
                    iter_item = item_deref["data"]

                yield node_key, iter_item
            else:
                yield "named_sub %d key" % named_sub_count, node_key
                yield "named_sub %d value" % named_sub_count, iter_item

            named_sub_count += 1
            if named_sub_count < size:
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
        return "array" if self.clion_representation else "map"


class InstructionPrettyPrinter:
    """
        instructiont causes problems with the default STL pretty-printers when
        they exist within collections. It attempts to perform a normal GDB pretty-print
        of the object as a 'summary' from a pointer, which then comes up against our
        exprt's and immediately times out and takes the debugging session with it.

        This pretty-printer fixes that bug, but comes with the unfortunate
        side-effect that you can't expand an instructiont in the CLion window, and
        instead have to perform a watch on it to look at internal values.

        It's the best solution out of a bunch of bad ones for now.
    """
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
    gdb.printing.register_pretty_printer(None, child_of_irept)

    printers = gdb.printing.RegexpCollectionPrettyPrinter("CBMC")

    # First argument is the name of the pretty-printer, second is a regex match for which type
    # it should be applied too, third is the class that should be called to pretty-print that type.
    printers.add_printer("dstringt", "^(?:dstringt|irep_idt)", DStringPrettyPrinter)
    printers.add_printer("instructiont", "^goto_programt::instructiont", InstructionPrettyPrinter)

    # We aren't associating with a particular object file, so pass in None instead of gdb.current_objfile()
    gdb.printing.register_pretty_printer(None, printers, replace=True)


def child_of_irept(val):
    """ Use the irep pretty-printer if we're a child of irept. Based on the
        assumption that all children will be using the sub/named_sub capabilities
        of irept and have no other internal fields. """

    type = untypedef(val.type)
    if type is None or type.name is None:
        return

    if type.code == gdb.TYPE_CODE_STRUCT \
            or type.code == gdb.TYPE_CODE_ENUM \
            or type.code == gdb.TYPE_CODE_UNION:

        hierarchy_types = set()
        while type is not None:
            if type.name is None or type.name in hierarchy_types:
                break
            else:
                hierarchy_types.add(type.name)

            for field in type.fields():
                if field.is_base_class:
                    type = untypedef(field.type)

        if "irept" in hierarchy_types:
            return IrepPrettyPrinter(val)

    return None
