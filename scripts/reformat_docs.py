import re, collections, textwrap, sys, argparse, platform

Field = collections.namedtuple('Field', ['name', 'contents'])

Header = collections.namedtuple('Header', ['module'])

Function = collections.namedtuple('Function',
        ['name', 'purpose', 'inputs', 'returns'])

Class = collections.namedtuple('Class', ['name', 'purpose'])


def warn(message):
    """ Print a labelled message to stderr.  """
    sys.stderr.write('Warning: %s\n' % message)


def header_from_block(block):
    """ Create a Header structure from a parsed Block.  """
    return Header(block.fields['Module'])


def function_from_block(block):
    """ Create a Function structure from a parsed Block.  """
    return Function(block.fields.get('Function', None),
            block.fields.get('Purpose', None), block.fields.get('Inputs', None),
            block.fields.get('Outputs', None))


def make_field(name, contents):
    return Field(name, contents if contents.strip() else None)


def class_from_block(block):
    """ Create a Class structure from a parsed Block.  """
    return Class(block.fields.get('Class', None),
            block.fields.get('Purpose', None))


def parse_fields(block_contents):
    """ Extract the named fields of an old-style comment block.  """

    field_re = re.compile(
            r'(?:\n *(Purpose):(.*))|(?:\n *([a-zA-Z0-9]+?):\n?(.*?)?^$)',
            re.MULTILINE | re.DOTALL)
    for m in field_re.finditer(block_contents):
        # If the field is a Purpose field
        if m.lastindex == 2:
            yield make_field(m.group(1), textwrap.dedent(m.group(2)))
        # If the field is any other field
        elif m.lastindex == 3 or m.lastindex == 4:
            yield make_field(m.group(3), textwrap.dedent(m.group(4)))


Block = collections.namedtuple('Block', ['fields'])


def has_field(block, field_name):
    """ Return whether the block has a field with the given name.  """
    return field_name in block.fields


def make_doxy_comment(text):
    text = re.sub(r'^(?!$)', r'/// ', text, flags=re.MULTILINE)
    return re.sub(r'^(?=$)', r'///' , text, flags=re.MULTILINE)


class GenericFormatter(object):
    def __init__(self, doc_width):
        self.text_wrapper = textwrap.TextWrapper(width=doc_width)
        self.indented_wrapper = textwrap.TextWrapper(width=doc_width,
                subsequent_indent=r'  ')
        self.whitespace_re = re.compile(r'\n\s*', re.MULTILINE | re.DOTALL)

    def convert(self, block):
        sections = filter(None, self.convert_sections(block))
        if sections:
            return make_doxy_comment('\n'.join(sections)) + '\n'
        return ''


class HeaderFormatter(GenericFormatter):
    def format_module(self, header):
        if not header.module:
            return None

        subbed = self.whitespace_re.sub(' ', header.module)
        # The file directive must be followed by a newline in order to refer to
        # the current file
        return '\\file\n' + self.indented_wrapper.fill(subbed)

    def is_block_valid(self, block):
        return has_field(block, 'Module')

    def convert_sections(self, block):
        return [self.format_module(block)]

    def needs_new_header(self, file_contents):
        return (re.search(r'^\/\/\/ \\file$', file_contents, flags=re.MULTILINE)
                is None)


class FunctionFormatter(GenericFormatter):
    def __init__(self, doc_width):
        super(FunctionFormatter, self).__init__(doc_width)
        self.paragraph_re = re.compile(r'(.*?)^$(.*)', re.MULTILINE | re.DOTALL)

    def format_purpose(self, function):
        if not function.purpose:
            return None

        match = self.paragraph_re.match(function.purpose)
        first_paragraph = match.group(1)
        first_paragraph = self.whitespace_re.sub(' ',
                first_paragraph) if first_paragraph else ''

        tail_paragraphs = (('\n' + match.group(2)) if match.group(2) else '')
        formatted_purpose = (self.text_wrapper.fill(first_paragraph) +
                tail_paragraphs)

        return formatted_purpose.strip()

    def format_inputs(self, function):
        if not function.inputs:
            return None

        if re.match(r'^\s*\S+\s*$', function.inputs):
            return None

        def param_replacement(match):
            return r'\param %s:' % match.group(1)

        lines = function.inputs.split('\n')
        tail = '\n'.join(lines[1:])

        dedented = lines[0] + '\n' + textwrap.dedent(tail)

        text = re.sub(r'\n\s+', ' ', dedented, flags=re.MULTILINE)
        text, num_replacements = re.subn(r'^([a-zA-Z0-9_]+)\s*[:-]',
                param_replacement, text, flags=re.MULTILINE)

        if num_replacements == 0:
            text = r'\par parameters: %s' % text

        text = '\n'.join(
                self.indented_wrapper.fill(t) for t in text.split('\n'))
        return text.strip()

    def format_returns(self, function):
        if not function.returns:
            return None

        subbed = self.whitespace_re.sub(' ', function.returns)
        return self.indented_wrapper.fill(r'\return %s' % subbed)

    def is_block_valid(self, block):
        return has_field(block, 'Function')

    def convert_sections(self, block):
        return [
            self.format_purpose(block),
            self.format_inputs(block),
            self.format_returns(block)]


class ClassFormatter(GenericFormatter):
    def __init__(self, doc_width):
        super(ClassFormatter, self).__init__(doc_width)
        self.paragraph_re = re.compile(r'(.*?)^$(.*)', re.MULTILINE | re.DOTALL)

    def format_purpose(self, klass):
        if not klass.purpose:
            return None

        match = self.paragraph_re.match(klass.purpose)
        first_paragraph = match.group(1)
        first_paragraph = self.whitespace_re.sub(' ',
                first_paragraph) if first_paragraph else ''

        tail_paragraphs = (('\n' + match.group(2)) if match.group(2) else '')
        formatted_purpose = (self.text_wrapper.fill(first_paragraph) +
                tail_paragraphs)

        return formatted_purpose.strip()

    def is_block_valid(self, block):
        return has_field(block, 'Class')

    def convert_sections(self, block):
        return [self.format_purpose(block)]


def replace_block(
        block_contents,
        file_contents,
        file,
        header_formatter,
        class_formatter,
        function_formatter):
    """
    Replace an old-style documentation block with the doxygen equivalent
    """
    block = Block(
            {f.name: f.contents for f in parse_fields(block_contents.group(1))})

    if header_formatter.is_block_valid(block):
        converted = header_formatter.convert(header_from_block(block))
        if header_formatter.needs_new_header(file_contents) and converted:
            return block_contents.group(0) + converted + '\n'
        return block_contents.group(0)

    if class_formatter.is_block_valid(block):
        return class_formatter.convert(class_from_block(block))

    if function_formatter.is_block_valid(block):
        return function_formatter.convert(function_from_block(block))

    warn('block in "%s" has unrecognised format:\n%s' %
            (file, block_contents.group(1)))

    return ''


def convert_file(file, inplace):
    """ Replace documentation in file with doxygen-styled comments.  """
    with open(file) as f:
        contents = f.read()

    doc_width = 76

    header_formatter = HeaderFormatter(doc_width)
    class_formatter = ClassFormatter(doc_width)
    function_formatter = FunctionFormatter(doc_width)

    block_re = re.compile(
            r'^/\*+\\$(.*?)^\\\*+/$\s*', re.MULTILINE | re.DOTALL)
    new_contents = block_re.sub(
            lambda match: replace_block(
                match,
                contents,
                file,
                header_formatter,
                class_formatter,
                function_formatter), contents)

    if inplace:
        with open(file, 'w') as f:
            f.write(new_contents)
    else:
        sys.stdout.write(new_contents)


def main():
    """ Run convert_file from the command-line.  """
    parser = argparse.ArgumentParser()
    parser.add_argument('file', type=str, help='The file to process')
    parser.add_argument('-i', '--inplace', action='store_true',
            help='Process in place')
    args = parser.parse_args()

    convert_file(args.file, args.inplace)

    return 0


if __name__ == '__main__':
    sys.exit(main())
