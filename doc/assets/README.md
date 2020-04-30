This folder contains resources for the documentation.

# XML Spec

The folllowing files relate to the specification of the XML trace output when using the `--xml-ui` flag.

## xml_spec.xsd
The`xml_spec.xsd` file is an XSD specification of the trace. You can validate an
output xml file from CBMC using the following invocation:

```bash
$ cbmc --xml-ui main.c | \
  xmllint --schema xml_spec.xsd --xpath "cprover/result/goto_trace" -
```

## xml_spec.tex

This is a LaTeX document describing the specification of the trace. It can be compiled to pdf using:

```bash
$ pdflatex -shell-escape xml_spec.tex
```

This requires:

 - texlive-latex-base
 - texlive-latex-extra (for minted package)
