import gdb
import pretty_printers


def build_pretty_printer_collection():
    
    printers = gdb.printing.RegexpCollectionPrettyPrinter("CBMC")
    
    # First argument is the name of the pretty-printer, second is a regex match for which type
    # it should be applied too, third is the class that should be called to pretty-print that type.
    printers.add_printer(
        'irep_idt', '^irep_idt', pretty_printers.DStringPrettyPrinter)
    printers.add_printer(
        'dstringt', '^dstringt', pretty_printers.DStringPrettyPrinter)
    printers.add_printer(
        'instructiont', '^goto_programt::instructiont', pretty_printers.InstructionPrettyPrinter)
    return printers


# If you change the name of this make sure to change install.py too.
def load_pretty_printers():

    # We aren't associating with a particular object file, so pass in None instead of gdb.current_objfile()
    gdb.printing.register_pretty_printer(None, build_pretty_printer_collection(), replace=True)
