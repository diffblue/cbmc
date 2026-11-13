#!/usr/bin/env python3

"""Validate SARIF 2.1.0 output from CBMC.

Reads SARIF JSON from stdin and validates:
- Valid JSON
- Required SARIF 2.1.0 top-level structure
- Required run/tool/results structure
- Required fields in each result object
- kind and level (SARIF 2.1.0 3.27.9, 3.27.10: only "fail" results may have
  a level other than "none")
- ruleIndex referring to a rule with the result's ruleId
- artifactLocation.uri being a URI reference (spaces etc. percent-encoded,
  absolute paths as file: URIs)
Exits 0 on success, 1 on validation failure.
"""

import json
import re
import sys

# RFC 3986 URI-reference: a scheme, or a relative reference whose characters
# are all unreserved, reserved or percent-encoded
URI_RE = re.compile(r"^([A-Za-z][A-Za-z0-9+.-]*:)?"
                    r"([A-Za-z0-9\-._~!$&'()*+,;=:@/?#\[\]]|%[0-9A-Fa-f]{2})*$")
VALID_KINDS = {"notApplicable", "pass", "fail", "review", "open",
               "informational"}


def validate_sarif(data):
    errors = []

    if not isinstance(data, dict):
        errors.append("Root must be a JSON object")
        return errors

    # Top-level fields
    if data.get("version") != "2.1.0":
        errors.append(
            f"Expected version '2.1.0', got '{data.get('version')}'")

    if "$schema" not in data:
        errors.append("Missing '$schema' field")

    if not isinstance(data.get("runs"), list) or len(data["runs"]) == 0:
        errors.append("'runs' must be a non-empty array")
        return errors

    for i, run in enumerate(data["runs"]):
        if not isinstance(run, dict):
            errors.append(f"runs[{i}] must be an object")
            continue

        # Tool
        tool = run.get("tool")
        if not isinstance(tool, dict):
            errors.append(f"runs[{i}].tool must be an object")
        else:
            driver = tool.get("driver")
            if not isinstance(driver, dict):
                errors.append(f"runs[{i}].tool.driver must be an object")
            else:
                if "name" not in driver:
                    errors.append(
                        f"runs[{i}].tool.driver.name is required")
        rules = []
        if isinstance(tool, dict) and isinstance(tool.get("driver"), dict):
            rules = tool["driver"].get("rules", [])

        # Results
        results = run.get("results")
        if not isinstance(results, list):
            errors.append(f"runs[{i}].results must be an array")
            continue

        for j, result in enumerate(results):
            if not isinstance(result, dict):
                errors.append(f"runs[{i}].results[{j}] must be an object")
                continue

            if "ruleId" not in result:
                errors.append(
                    f"runs[{i}].results[{j}].ruleId is required")

            if "message" not in result:
                errors.append(
                    f"runs[{i}].results[{j}].message is required")
            elif "text" not in result.get("message", {}):
                errors.append(
                    f"runs[{i}].results[{j}].message.text is required")

            level = result.get("level")
            valid_levels = {"none", "note", "warning", "error"}
            if level is not None and level not in valid_levels:
                errors.append(
                    f"runs[{i}].results[{j}].level '{level}' "
                    f"not in {valid_levels}")

            kind = result.get("kind", "fail")
            if kind not in VALID_KINDS:
                errors.append(
                    f"runs[{i}].results[{j}].kind '{kind}' not in "
                    f"{VALID_KINDS}")
            if kind != "fail" and level not in (None, "none"):
                errors.append(
                    f"runs[{i}].results[{j}]: kind '{kind}' requires level "
                    f"'none', got '{level}'")

            if "ruleIndex" in result:
                index = result["ruleIndex"]
                if not (isinstance(index, int) and 0 <= index < len(rules)):
                    errors.append(
                        f"runs[{i}].results[{j}].ruleIndex {index} out of "
                        f"range")
                elif rules[index].get("id") != result.get("ruleId"):
                    errors.append(
                        f"runs[{i}].results[{j}].ruleIndex {index} does not "
                        f"refer to rule '{result.get('ruleId')}'")

            # Validate locations structure if present
            locations = result.get("locations", [])
            for k, loc in enumerate(locations):
                if not isinstance(loc, dict):
                    errors.append(
                        f"runs[{i}].results[{j}].locations[{k}] "
                        f"must be an object")
                    continue
                pl = loc.get("physicalLocation", {})
                if not isinstance(pl, dict):
                    errors.append(
                        f"runs[{i}].results[{j}].locations[{k}]"
                        f".physicalLocation must be an object")
                    continue
                if "artifactLocation" in pl:
                    al = pl["artifactLocation"]
                    if not isinstance(al, dict):
                        errors.append(
                            f"runs[{i}].results[{j}].locations[{k}]"
                            f".physicalLocation.artifactLocation "
                            f"must be an object")
                        continue
                    if "uri" not in al:
                        errors.append(
                            f"runs[{i}].results[{j}].locations[{k}]"
                            f".physicalLocation.artifactLocation.uri "
                            f"is required")
                    elif (not URI_RE.match(al["uri"]) or
                          al["uri"].startswith("/")):
                        errors.append(
                            f"runs[{i}].results[{j}].locations[{k}]"
                            f".physicalLocation.artifactLocation.uri "
                            f"'{al['uri']}' is not a valid URI reference")

    return errors


def main():
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            raw = f.read()
    else:
        raw = sys.stdin.read()

    try:
        data = json.loads(raw)
    except json.JSONDecodeError as e:
        print(f"SARIF VALIDATION FAILED: Invalid JSON: {e}")
        return 1

    errors = validate_sarif(data)
    if errors:
        print("SARIF VALIDATION FAILED:")
        for error in errors:
            print(f"  - {error}")
        return 1

    n_results = sum(
        len(run.get("results", []))
        for run in data.get("runs", []))
    print(f"SARIF VALIDATION SUCCESSFUL ({n_results} results)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
