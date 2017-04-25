import re, collections, textwrap, sys, argparse, platform


Field = collections.namedtuple('Field', ['name', 'contents'])

Header = collections.namedtuple('Header', ['module'])

Function = collections.namedtuple('Function',
        ['pos', 'name', 'purpose', 'inputs', 'returns'])

Class = collections.namedtuple('Class', ['name', 'purpose'])


def warn(message):
    """ Print a labelled message to stderr.  """
    sys.stderr.write('Warning: %s\n' % message)


def header_from_block(block):
    """ Create a Header structure from a parsed Block.  """
    return Header(block.fields['Module'])


def function_from_block(block):
    """ Create a Function structure from a parsed Block.  """
    return Function(block.pos, block.fields.get('Function', None),
            block.fields.get('Purpose', None), block.fields.get('Inputs', None),
            block.fields.get('Outputs', None))


def class_from_block(block):
    """ Create a Class structure from a parsed Block.  """
    return Class(block.fields.get('Class', None),
            block.fields.get('Purpose', None))


def parse_fields(block_contents, width):
    """ Extract the named fields of an old-style comment block.  """

    field_re = re.compile(
            r'(?:\n *(Purpose):(.*))|(?:\n *([a-zA-Z0-9]+?):\n?(.*?)?^$)',
            re.MULTILINE | re.DOTALL)
    for m in field_re.finditer(block_contents):
        # If the field is a Purpose field
        if m.lastindex == 2:
            yield Field(m.group(1), textwrap.dedent(m.group(2)))
        # If the field is any other field
        elif m.lastindex == 3 or m.lastindex == 4:
            yield Field(m.group(3), textwrap.dedent(m.group(4)))


Block = collections.namedtuple('Block', ['pos', 'fields'])


def has_field(block, field_name):
    """ Return whether the block has a field with the given name.  """
    return field_name in block.fields


def make_doxy_comment(text):
    text, _ = re.subn(r'^(?!$)', r'/// ', text, flags=re.MULTILINE)
    text, _ = re.subn(r'^(?=$)', r'///' , text, flags=re.MULTILINE)
    return text


def is_header_doc(block):
    """ Return whether the block appears to be a file header.  """
    return has_field(block, 'Module')


def convert_header_doc(header, doc_width):
    """ Return a doxygen-style header string.  """
    text_wrapper = textwrap.TextWrapper(width=doc_width)
    return (make_doxy_comment(
            text_wrapper.fill(r'\file %s' % header.module)) + '\n\n'
            if header.module.strip() else '')


def is_function_doc(block):
    """ Return whether the block appears to be a function descriptor.  """
    return has_field(block, 'Function')


class FunctionFormatter:
    def __init__(self, doc_width):
        self.text_wrapper = textwrap.TextWrapper(width=doc_width)
        self.input_wrapper = textwrap.TextWrapper(width=doc_width,
                subsequent_indent=r'  ')
        self.whitespace_re = re.compile(r'\n\s*', re.MULTILINE | re.DOTALL)
        self.paragraph_re = re.compile(r'(.*?)^$(.*)', re.MULTILINE | re.DOTALL)

    def format_purpose(self, function):
        match = self.paragraph_re.match(function.purpose)
        first_paragraph = match.group(1)
        first_paragraph, _ = self.whitespace_re.subn(' ',
                first_paragraph) if first_paragraph else ('', None)

        tail_paragraphs = (('\n' + match.group(2)) if match.group(2) else '')
        formatted_purpose = (self.text_wrapper.fill(first_paragraph) +
                tail_paragraphs)

        return formatted_purpose.strip()

    def format_inputs(self, function):
        def param_replacement(match):
            return r'\param %s:' % match.group(1)

        dedented = textwrap.dedent(function.inputs)
        text, _ = re.subn(r'\n\s+', ' ', dedented, flags=re.MULTILINE)
        text, num_replacements = re.subn(r'^([a-zA-Z0-9_]+)\s+[:-]',
                param_replacement, text, flags=re.MULTILINE)

        if num_replacements == 0:
            text = r'parameters: %s' % text

        text = '\n'.join(self.input_wrapper.fill(t) for t in text.split('\n'))
        return text.strip()

    def format_returns(self, function):
        subbed, _ = self.whitespace_re.subn(' ', function.returns)
        return self.input_wrapper.fill(r'\returns %s' % subbed)


def convert_function_doc(function, file, doc_width):
    """ Return a doxygen-style doc string for the supplied Function.  """
    formatter = FunctionFormatter(doc_width)

    sections = []

    if function.purpose and function.purpose.strip():
        sections.append(formatter.format_purpose(function))

    if function.inputs and function.inputs.strip():
        sections.append(formatter.format_inputs(function))

    if function.returns and function.returns.strip():
        sections.append(formatter.format_returns(function))

    if sections:
        text = '\n\n'.join(sections)
        if text:
            text = make_doxy_comment(text)
        return text + '\n'

    return ''


def is_class_doc(block):
    """ Return whether the block appears to be a class doc block.  """
    return has_field(block, 'Class')


def convert_class_doc(c, doc_width):
    """ Return a doxygen-style class string.  """
    text_wrapper = textwrap.TextWrapper(width=doc_width)
    stripped = c.purpose.strip()
    return (make_doxy_comment(text_wrapper.fill(stripped)) + '\n'
            if stripped else '')


def replace_block(start, block_contents, file, doc_width):
    """
    Replace an old-style documentation block with the doxygen equivalent
    """
    block = Block(start,
            {f.name: f.contents
                for f in parse_fields(block_contents, doc_width)})

    if is_header_doc(block):
        return convert_header_doc(header_from_block(block), doc_width)

    if is_function_doc(block):
        return convert_function_doc(
                function_from_block(block), file, doc_width)

    if is_class_doc(block):
        return convert_class_doc(class_from_block(block), doc_width)

    warn('block in "%s" has unrecognised format:\n%s' %
            (file, block_contents))

    return ''


def convert_file(file):
    """ Replace documentation in file with doxygen-styled comments.  """
    with open(file) as f:
        contents = f.read()

    doc_width = 75

    block_re = re.compile(
            r'^/\*+\\$(.*?)^\\\*+/$\s*', re.MULTILINE | re.DOTALL)
    contents, _ = block_re.subn(
            lambda match: replace_block(match.start(), match.group(1), file,
                doc_width), contents)

    sys.stdout.write(contents)


def main():
    """ Run convert_file from the command-line.  """
    parser = argparse.ArgumentParser()
    parser.add_argument('file', type=str, help='The file to process')
    args = parser.parse_args()

    convert_file(args.file)

    return 0


if __name__ == '__main__':
    sys.exit(main())
