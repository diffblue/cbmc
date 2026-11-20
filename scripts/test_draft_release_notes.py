#!/usr/bin/env python3
"""Unit tests for scripts/draft_release_notes.py.

Run with: python3 -m pytest scripts/test_draft_release_notes.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import draft_release_notes as drn


def test_version_key():
    assert drn.version_key("cbmc-6.8.0") == [6, 8, 0]
    assert drn.version_key("cbmc-6.8") == [6, 8]
    assert drn.version_key("cbmc-10.2.3") == [10, 2, 3]


def test_select_previous_tag_basic():
    tags = ["cbmc-6.8.0", "cbmc-6.7.1", "cbmc-6.7.0"]
    assert drn.select_previous_tag(tags, "cbmc-6.8.0") == "cbmc-6.7.1"


def test_select_previous_tag_orders_numerically():
    # lexical ordering would put cbmc-6.10.0 before cbmc-6.9.0
    tags = ["cbmc-6.9.0", "cbmc-6.10.0", "cbmc-6.8.0"]
    assert drn.select_previous_tag(tags, "cbmc-6.10.0") == "cbmc-6.9.0"


def test_select_previous_tag_ignores_suffixed_tags():
    # conference/hash-suffixed tags must be filtered so they cannot be confused
    # with the corresponding bare version when choosing the predecessor
    tags = [
        "cbmc-4.6",
        "cbmc-4.5",
        "cbmc-4.5-sv-comp-2014",
        "cbmc-4.8-incremental",
        "cbmc-5.12-d8598f8",
    ]
    assert drn.select_previous_tag(tags, "cbmc-4.6") == "cbmc-4.5"


def test_select_previous_tag_new_tag_not_present():
    tags = ["cbmc-6.7.1", "cbmc-6.7.0"]
    # the tag being released may not exist yet -> latest existing release tag
    assert drn.select_previous_tag(tags, "cbmc-6.8.0") == "cbmc-6.7.1"


def test_select_previous_tag_none_when_no_release_tags():
    assert drn.select_previous_tag(["v1.0", "random-tag"], "cbmc-1.0") is None


FEATURE_NOTES = """## What's Changed
* Add quantifier support by @alice in https://github.com/diffblue/cbmc/pull/8921
* Implement bitwise intrinsics by @bob in https://github.com/diffblue/cbmc/pull/8923
* Fix a crash by @carol in https://github.com/diffblue/cbmc/pull/8930
* Bump action-gh-release from 2 to 3 by @dependabot in https://github.com/diffblue/cbmc/pull/8957
"""

NO_FEATURE_NOTES = """## What's Changed
* Fix a crash by @carol in https://github.com/diffblue/cbmc/pull/8930
* Refactor internals by @dave in https://github.com/diffblue/cbmc/pull/8931
"""


def test_draft_summary_features_and_others():
    s = drn.draft_summary(FEATURE_NOTES, "6.9.0")
    assert s.comment.startswith("<!-- DRAFT")
    assert s.body.startswith("This release includes ")
    assert "Add quantifier support (via #8921)" in s.body
    assert "Implement bitwise intrinsics (via #8923)" in s.body
    # the dependabot bump is skipped; "Fix a crash" is the single other change
    assert "1 other change." in s.body
    assert "other changes" not in s.body  # singular


def test_draft_summary_no_features_is_todo():
    s = drn.draft_summary(NO_FEATURE_NOTES, "6.9.0")
    assert s.comment == "<!-- TODO: write a summary for CBMC 6.9.0 -->"
    assert s.body == ""


def test_format_release_notes_todo_has_no_prose_body():
    out = drn.format_release_notes(NO_FEATURE_NOTES, "6.9.0")
    assert out.startswith("# CBMC 6.9.0\n\n")
    assert "<!-- TODO: write a summary for CBMC 6.9.0 -->" in out
    assert "This release includes" not in out
    assert "Fix a crash" in out  # the generated notes are appended verbatim


def test_format_release_notes_features_wraps_prose():
    out = drn.format_release_notes(FEATURE_NOTES, "6.9.0")
    assert out.startswith("# CBMC 6.9.0\n\n<!-- DRAFT")
    assert "This release includes" in out
    # the prose body is wrapped; the verbatim PR list lines are not
    for line in out.splitlines():
        assert len(line) <= 80 or line.lstrip().startswith("*")


if __name__ == "__main__":
    sys.exit(__import__("pytest").main([__file__, "-v"]))
