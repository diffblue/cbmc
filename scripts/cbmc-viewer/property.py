"""The properties tested for by a run of cbmc."""

import srcloc as SrcLoc

# pylint: disable=too-few-public-methods

################################################################

class Property:
    """The properties checked by cbmc."""

    def __init__(self, xml="", srcloc=None):
        """
        Initialize properties with output of 'cbmc --show-properties --xml-ui'.
        """

        self.property = {}

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

    def lookup(self, name):
        """Look up a property by property name."""
        return self.property.get(name, None)

################################################################
