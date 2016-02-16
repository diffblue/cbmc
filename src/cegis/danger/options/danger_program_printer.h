#ifndef CEGIS_DANGER_PROGRAM_PRINTER_H_
#define CEGIS_DANGER_PROGRAM_PRINTER_H_

#include <util/message.h>

/**
 * @brief
 *
 * @details
 *
 * @param os
 * @param program
 * @param solution
 */
void print_danger_program(messaget::mstreamt &os,
    const class danger_programt &program,
    const class danger_goto_solutiont &solution);

#endif /* CEGIS_DANGER_PROGRAM_PRINTER_H_ */
