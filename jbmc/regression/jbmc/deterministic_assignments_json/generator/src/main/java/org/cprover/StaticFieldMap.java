package org.cprover;

import java.util.HashMap;

/**
 * A map whose keys are of type String.
 * We use this instead of e.g. HashMap and define a custom writer for it because
 * json-io prints Maps in a special way that would ignore our custom String
 * writer for both the keys and values of the Map. We want to use the custom
 * String writer for values but not for keys.
 */
public class StaticFieldMap<V> extends HashMap<String, V> {
}
