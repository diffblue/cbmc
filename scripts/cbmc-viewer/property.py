"""The properties tested for by a run of cbmc."""

import srcloc as SrcLoc

# pylint: disable=too-few-public-methods


class Property:
    """The properties checked by cbmc."""

    def __init__(self):
        """Initialize properties."""
        self.property = {}

    def lookup(self, name):
        """Look up a property by property name."""
        return self.property.get(name, None)


class PropertyCBMC(Property):
    """ The properties checked by cbmc.

    This subclass of Property assumes the properties are described in an xml
    file produced by a run of cbmc with 'cbmc --show-properties --xml-ui'.
    """

    def __init__(self, xml="", srcloc=None):
        """Initialize properties with output of
        'cbmc --show-properties --xml-ui'.
        """
        super(PropertyCBMC, self).__init__()

        if xml == "":
            return

        root = SrcLoc.parse_xml_file(xml)
        srcloc.scan_source_locations(root)

        for prop in root.iter("property"):
            name = prop.get("name")
            cls = prop.get("class")
            src = prop.find("location").get("file")
            line = prop.find("location").get("line")
            func = prop.find("location").get("function")
            desc = prop.find("description").text
            expr = prop.find("expression").text

            # Some properties are not mapped to a source location.
            if src:
                src = srcloc.clean_path(src)
            else:
                src = "built-in"
                line = "-1"

            self.property[name] = {"name":  name,
                                   "class": cls,
                                   "file": src,
                                   "line": line,
                                   "function": func,
                                   "description": desc,
                                   "expression": expr}


class PropertyStorm(Property):
    """ The properties checked by cbmc.

    This subclass of Property assumes the properties are described in a log
    file produced by a run of cbmc-storm.
    """

    def __init__(self, storm):
        """Initialize properties with output of cbmc-storm."""
        super(PropertyStorm, self).__init__()

        for name in storm.property:
            prop = storm.property[name]
            self.property[name] = {"name":  name,
                                   "class": "",
                                   "file": prop['file'],
                                   "line": prop['line'],
                                   "function": prop['func'],
                                   "description": prop['desc'],
                                   "expression": prop['expr']}

################################################################
