#!/usr/bin/env python3

# https://pandoc.org/MANUAL.html
# https://pandoc.org/filters.html
# AST: https://hackage.haskell.org/package/pandoc-types-1.22.2.1/docs/Text-Pandoc-Definition.html

from pandocfilters import toJSONFilter, Link

def patch_url(url):

    # cbmc-tutorial.md links directly to source files used in examples; link to local copies instead
    raw_url = 'https://raw.githubusercontent.com/diffblue/cbmc/develop/doc/cprover-manual/'
    if url.startswith(raw_url):
        return url[len(raw_url):]

    if url.startswith('http://') or url.startswith('https://'):
        return url

    try:
        path, label = url.rsplit('#', 1)
    except ValueError:
        path, label = url, ''

    # Flatten hierarchical urls in cprover-manual to a flat set of markdown files
    # Map a url like ../../helpful/cow/ to helpful-cow.md
    # Map a url like . or .. to . (not index.md since index.md is doxygen mainpage)

    parts = [part for part in path.split('/') if part and part != '.' and part != '..']
    new_path = '-'.join(parts) + '.md' if parts else ''

    new_url = f'{new_path}#{label}' if label else new_path
    if new_url:
        return new_url
    return '.'

def test_patch_url():
    assert patch_url("../../helpful/cow/") == "helpful-cow.md"
    assert patch_url("helpful/cow") == "helpful-cow.md"
    assert patch_url("helpful/cow/") == "helpful-cow.md"
    assert patch_url("helpful-cow/") == "helpful-cow.md"

def patch_link(key, value, _format, _meta):
    if key == 'Link':
        attr, alt_text, link = value
        url, title = link
        return Link(attr, alt_text, [patch_url(url), title])
    return None

if __name__ == "__main__":
    toJSONFilter(patch_link)
