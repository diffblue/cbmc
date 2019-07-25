#!/usr/bin/env python3

import os
from shutil import copyfile


def create_gdbinit_file():
    """
    Create and insert into a .gdbinit file the python code to set-up cbmc pretty-printers.
    """

    print("Attempting to enable cbmc-specific pretty-printers.")

    home_folder = os.path.expanduser("~")
    if not home_folder:
        print(home_folder + " is an invalid home folder, can't auto-configure .gdbinit.")
        return

    # This is the code that should be copied if you're applying the changes by hand.
    gdb_directory = os.path.dirname(os.path.abspath(__file__))
    code_block_start = "cbmc_printers_folder = "
    code_block = \
        [
            "{0}'{1}'".format(code_block_start, gdb_directory),
            "if os.path.exists(cbmc_printers_folder):",
            "    sys.path.insert(1, cbmc_printers_folder)",
            "    from pretty_printers import load_cbmc_printers",
            "    load_cbmc_printers()",
        ]

    gdbinit_file = os.path.join(home_folder, ".gdbinit")
    lines = []
    imports = { "os", "sys" }
    if os.path.exists(gdbinit_file):
        with open(gdbinit_file, 'r') as file:
            lines = [ line.rstrip() for line in file ]
        line_no = 0
        while line_no < len(lines):
            if lines[line_no].startswith('import '):
                imports.add(lines[line_no][len("import "):].strip())
                lines.pop(line_no)
            else:
                if lines[line_no].startswith(code_block_start):
                    print(".gdbinit already contains our pretty printers, not changing it")
                    return
                line_no += 1
        while len(lines) != 0 and (lines[0] == "" or lines[0] == "python"):
            lines.pop(0)

        backup_file = os.path.join(home_folder, "backup.gdbinit")
        if os.path.exists(backup_file):
            print("backup.gdbinit file already exists. Type 'y' if you would like to overwrite it or any other key to exit.")
            choice = input().lower()
            if choice != 'y':
                return
        print("Backing up {0}".format(gdbinit_file))
        copyfile(gdbinit_file, backup_file)

    lines = [ "python" ] + list(map("import {}".format, sorted(imports))) + [ "", "" ] + code_block + [ "", "" ] + lines + [ "" ]
    print("Adding pretty-print commands to {0}.".format(gdbinit_file))
    try:
        with open(gdbinit_file, 'w+') as file:
            file.write('\n'.join(lines))
        print("Commands added.")
    except:
        print("Exception occured writing to file. Please apply changes manually.")


if __name__ == "__main__":
    create_gdbinit_file()
