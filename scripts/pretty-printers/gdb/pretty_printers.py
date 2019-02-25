import gdb


class DStringPrettyPrinter:
    def __init__(self, val):
        self.val = val

    def to_string(self):
        try:
            raw_address = str(self.val.address)

            # If it's ::empty, we know it's empty without going further.
            if "::empty" in raw_address:
                return ""

            # Split the address on the first space, return that value
            # Addresses are usually {address} {optional type_name}
            typed_pointer = '({}*){}'.format(self.val.type, raw_address.split(None, 1)[0])

            # Check that the pointer is not null.
            if gdb.parse_and_eval(typed_pointer + ' == 0'):
                return ""

            # If it isn't attempt to find the string.
            value = '(*{})'.format(typed_pointer)
            return gdb.parse_and_eval(value + '.c_str()')
        except:
            return ""

    def display_hint(self):
        return 'string'


class InstructionPrettyPrinter:
    def __init__(self, val):
        self.val = val

    def to_string(self):
        try:
            raw_address = str(self.val.address)
            variable_accessor = '(*({}*){})'.format(self.val.type, raw_address.split(None, 1)[0])
            expr = '{0}.to_string()'.format(variable_accessor)
            return gdb.parse_and_eval(expr)
        except:
            return ""

    def display_hint(self):
        return 'string'
