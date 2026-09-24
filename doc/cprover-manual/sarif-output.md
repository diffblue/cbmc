[CPROVER Manual TOC](../)

# SARIF Output

CBMC and JBMC support [SARIF](https://sarifweb.azurewebsites.net/) (Static
Analysis Results Interchange Format) output, which is widely supported by IDEs
and CI systems. Use `--sarif-result` to write SARIF output to a file:

```
    cbmc file1.c --bounds-check --pointer-check --sarif-result results.sarif
```

Use `-` as the filename to write to standard output. The `--sarif-result`
option can be combined with other UI modes (e.g., `--json-ui`, `--xml-ui`),
producing both the normal output and a SARIF file.

This produces a JSON document conforming to the SARIF 2.1.0 schema, with each
property reported as a SARIF result entry including rule identifier, result
kind, severity level, message, and source location. Passing and not-applicable
properties are reported with a non-`fail` kind and `level: "none"` so that
SARIF consumers (such as GitHub code scanning) do not surface a verified
program as a wall of findings. For example:

```json
{
  "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
  "version": "2.1.0",
  "runs": [{
    "tool": {
      "driver": {
        "name": "cbmc",
        "version": "...",
        "informationUri": "https://www.cprover.org/cbmc/"
      }
    },
    "results": [{
      "ruleId": "main.assertion.1",
      "kind": "fail",
      "level": "error",
      "message": { "text": "assertion x > 0 (FAILURE)" },
      "locations": [{
        "physicalLocation": {
          "artifactLocation": { "uri": "example.c" },
          "region": { "startLine": 5 }
        }
      }]
    }]
  }]
}
```
