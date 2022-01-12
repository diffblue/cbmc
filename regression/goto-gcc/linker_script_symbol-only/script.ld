MEMORY {
  RAM : ORIGIN = 0x0, LENGTH = 25M
}

SECTIONS
{
  /* GCC insists on having these */
  .note.gnu.build-id : { } > RAM
  .text : { } > RAM

  .src_section : {
    sym = .;
    *(.text*)
  } > RAM
}
