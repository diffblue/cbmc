[CPROVER Manual TOC](../)

# SARIF Output

CBMC and JBMC can write their verification results in
[SARIF](https://sarifweb.azurewebsites.net/) 2.1.0 (Static Analysis Results
Interchange Format), which IDEs and CI systems can read. Use `--sarif-result`
to write the results to a file:

```
    cbmc file1.c --bounds-check --pointer-check --sarif-result results.sarif
```

The file is opened before verification starts, so a file that cannot be
written is reported as a usage error. `--sarif-result` can be combined with the
other UI modes (e.g., `--json-ui`, `--xml-ui`), which then produce their usual
output on standard output. Use `-` as the file name to write the SARIF log to
standard output instead; this cannot be combined with `--json-ui` or
`--xml-ui`, and only warnings and errors are then printed, on standard error.
Options that do not perform verification, such as `--show-properties` or
`--cover`, do not produce a SARIF log.

Each property is reported as one SARIF result:

* `ruleId` is the property class, such as `assertion`, `array_bounds` or
  `pointer_dereference`; each class is listed once in `tool.driver.rules`. The
  property's own identifier (e.g. `main.assertion.1`) is given as
  `properties.propertyId`, as it changes when properties are added.
* `kind` is `fail` for a failed property, which then has `level` `error`; it
  is `pass` for a property that holds, `open` if the result is not known (e.g.
  with `--stop-on-fail`), and `notApplicable` for properties that are not
  reachable or not checked. As SARIF requires, results other than failures
  have no level (that is, level `none`). Consumers that only look at the
  level, rather than the kind, may still list such results.
* `locations` gives the source file as a URI (an absolute path as a `file:`
  URI, with characters such as spaces percent-encoded), the line and column,
  and the function as a logical location. Properties without a source file,
  such as those in built-in library functions, only have the logical
  location.

For example:

```json
{
  "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
  "version": "2.1.0",
  "runs": [{
    "tool": {
      "driver": {
        "name": "cbmc",
        "version": "...",
        "informationUri": "https://www.cprover.org/cbmc/",
        "rules": [{
          "id": "assertion",
          "shortDescription": { "text": "assertion" }
        }]
      }
    },
    "results": [{
      "ruleId": "assertion",
      "ruleIndex": 0,
      "kind": "fail",
      "level": "error",
      "message": { "text": "assertion x > 0 (FAILURE)" },
      "locations": [{
        "physicalLocation": {
          "artifactLocation": { "uri": "example.c" },
          "region": { "startLine": 5 }
        },
        "logicalLocations": [{
          "fullyQualifiedName": "main",
          "kind": "function"
        }]
      }],
      "properties": { "propertyId": "main.assertion.1" }
    }]
  }]
}
```
