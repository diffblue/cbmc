/*
 * 1. Iterate over all functions
 * 2. Iterate over all instructions
 * 3. Find back-edges (well, ideally, use the loop finder to find loop
 * back edges)
 * 4. goto_program::loop_id(function_id, instruction)
 * 5. Iterate over the histories, find the max number of consequetive
 * times this is visited -- but is it that because of nested loops and
 * if statements in loops
 *
 * Not clear where to store information, an unwindsett?
 */

