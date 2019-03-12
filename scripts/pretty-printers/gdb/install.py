#!/usr/bin/env python

import os

# This is the code that should be copied if you're applying the changes by hand.
# Replace {0} with the path to this folder.
file_contents = """
python
import sys
import os

pretty_printer_folder = '{0}'
if os.path.exists(pretty_printer_folder):
    sys.path.insert(1, pretty_printer_folder)
    import auto_load
    auto_load.load_pretty_printers()
end
"""


def create_gdbinit_file():
    """
    Add or append to a .gdbinit file the python code to set-up cbmc pretty-printers.
    """

    print("Attempting to enable cbmc-specific pretty-printers.")

    home_folder = os.path.expanduser("~")
    if not home_folder:
        print(home_folder + " is an invalid home folder, please manually create a .gdbinit file and apply the code.")
        return

    gdbinit_file = os.path.join(home_folder, ".gdbinit")
    file_write_mode = 'w'
    if os.path.exists(gdbinit_file):
        print(".gdbinit file exists at " + gdbinit_file + "."
              " Please type 'y' if you want to append the pretty-printer commands to it. Press any other key to exit.")
        while True:
            choice = input().lower()
            if choice == 'y':
                file_write_mode = 'a'
                break
            else:
                print("Not appending to file. Exiting.")
                return

    if file_write_mode == 'w':
        print("Creating .gdbinit file.")

    print("Adding pretty-print commands to {0}.".format(gdbinit_file))
    parent_directory = os.path.dirname(os.path.abspath(__file__))
    try:
        file = open(gdbinit_file, file_write_mode)
        file.write(file_contents.format(parent_directory))
        file.close()
        print("Commands added.")
    except:
        print("Exception occured writing to file. Please apply changes manually.")


if __name__ == "__main__":
    create_gdbinit_file()

