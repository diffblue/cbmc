package org.cprover;

/**
 * This can be added to methods to indicate they aren't allowed to throw
 * exceptions. JBMC and related tools will truncate any execution path on which
 * they do with an ASSUME FALSE instruction.
 */
public @interface MustNotThrow { }
