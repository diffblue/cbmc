#!/usr/bin/env python3
"""
Generate draft release notes for a CBMC release.

Calls the GitHub release-notes generation endpoint (the same one behind
the "Generate release notes" button in the GitHub UI) and prepends a
draft summary paragraph derived from the PR titles.

The tag need not exist yet; when auto-detecting the previous tag the
script falls back to the latest existing tag.

This is a CBMC-specific helper: the release-tag prefix and the "# CBMC"
heading are hard-coded for the diffblue/cbmc repository.

Usage:
    scripts/draft_release_notes.py cbmc-6.8.0
    scripts/draft_release_notes.py cbmc-6.8.0 --previous cbmc-6.7.1
"""

import json
import re
import subprocess
import sys
import textwrap
from dataclasses import dataclass

REPO = "diffblue/cbmc"


def run_gh(args):
    """Run a `gh` command and return its stdout.

    Exits cleanly (rather than dumping a stack trace) when `gh` is missing or
    the call fails, e.g. due to authentication or network problems.
    """
    try:
        result = subprocess.run(
            ["gh", *args], capture_output=True, text=True, check=True
        )
    except FileNotFoundError:
        sys.exit(
            "error: the GitHub CLI ('gh') was not found; please install it "
            "(https://cli.github.com/) and authenticate with 'gh auth login'."
        )
    except subprocess.CalledProcessError as e:
        sys.exit(f"error: 'gh {' '.join(args)}' failed:\n{e.stderr.strip()}")
    return result.stdout


def gh_generate_notes(tag: str, previous: str) -> str:
    """Call the GitHub generate-notes API via `gh`."""
    stdout = run_gh([
        "api", f"repos/{REPO}/releases/generate-notes",
        "-f", f"tag_name={tag}",
        "-f", f"previous_tag_name={previous}",
    ])
    return json.loads(stdout)["body"]


# A release tag of the form cbmc-X.Y or cbmc-X.Y.Z. Tags carrying extra
# suffixes (e.g. cbmc-4.5-sv-comp-2014, cbmc-4.8-incremental, cbmc-5.12-d8598f8)
# are intentionally excluded so they cannot be confused with the corresponding
# bare version when ordering.
_RELEASE_TAG = re.compile(r"^cbmc-\d+\.\d+(?:\.\d+)?$")


def version_key(tag: str):
    """Sort key: the numeric (major, minor, patch) components of a release tag.

    \\pre `tag` matches `_RELEASE_TAG`.
    """
    return [int(p) for p in tag.split("-", 1)[1].split(".")]


def select_previous_tag(all_tags, tag: str):
    """Return the release tag immediately preceding `tag`.

    Only tags matching `_RELEASE_TAG` are considered. If `tag` itself is not
    present (it may not have been created yet), the latest existing release
    tag is returned. Returns None if there is no release tag at all.
    """
    tags = sorted(
        (t for t in all_tags if _RELEASE_TAG.match(t)),
        key=version_key,
        reverse=True,
    )
    for i, t in enumerate(tags):
        if t == tag and i + 1 < len(tags):
            return tags[i + 1]
    return tags[0] if tags else None


def previous_tag(tag: str) -> str:
    """Find the release tag immediately before `tag` using `gh`."""
    stdout = run_gh([
        "api", f"repos/{REPO}/tags", "--paginate", "-q", ".[].name",
    ])
    result = select_previous_tag(stdout.splitlines(), tag)
    if result is None:
        sys.exit(f"Cannot find a tag before {tag}")
    return result


def version_from_tag(tag: str) -> str:
    return tag.split("-", 1)[1]


# Patterns for changes that are NOT user-facing
_SKIP = re.compile(
    r"(?i)"
    r"\bbump\b|dependabot|"
    r"\bCI\b|ci:|ci job|GitHub Action|runner|"
    r"Compile Java regression|"
    r"CODEOWNERS|"
    r"clang-format|"
    r"Release CBMC"
)

# Patterns that suggest a user-visible feature (not just a fix/refactor)
_FEATURE = re.compile(
    r"(?i)"
    r"\badd\b|\bimplement\b|\bintroduce\b|\bsupport\b|\bnew\b|\benable\b"
)


@dataclass
class DraftSummary:
    """A drafted summary, split into its HTML comment line and prose body."""

    comment: str  # leading HTML comment (a DRAFT or TODO marker)
    body: str  # prose sentence(s); empty when only a TODO is emitted


def _join_highlights(highlights):
    if len(highlights) == 1:
        return highlights[0]
    if len(highlights) == 2:
        return f"{highlights[0]} and {highlights[1]}"
    return f"{highlights[0]}, {highlights[1]}, and {highlights[2]}"


def draft_summary(notes: str, version: str) -> DraftSummary:
    """Build a draft summary from the GitHub-generated notes.

    Strategy: highlight the top user-visible feature PRs and count the
    remaining (non-feature) changes. This is a *draft* — the release manager
    must review and edit it. When no user-visible feature can be identified,
    a TODO placeholder is emitted rather than guessing.
    """
    # Extract PR lines: "* <title> by @author in <url>"
    pr_lines = [
        line.strip()
        for line in notes.splitlines()
        if line.strip().startswith("* ")
    ]

    # Filter to user-facing changes, splitting into features and other changes
    # (the latter covers bug fixes, refactors, documentation, etc.).
    visible = [l for l in pr_lines if not _SKIP.search(l)]
    features = [l for l in visible if _FEATURE.search(l)]
    others = [l for l in visible if l not in features]

    if not features:
        return DraftSummary(
            comment=f"<!-- TODO: write a summary for CBMC {version} -->",
            body="",
        )

    def extract(line: str):
        m = re.match(r"\*\s+(.+?)\s+by\s+@", line)
        title = m.group(1) if m else line.lstrip("* ")
        m2 = re.search(r"/pull/(\d+)", line)
        pr = m2.group(1) if m2 else None
        return title, pr

    highlights = []
    for line in features[:3]:
        title, pr = extract(line)
        ref = f" (via #{pr})" if pr else ""
        highlights.append(f"{title}{ref}")

    prose = f"This release includes {_join_highlights(highlights)}."
    n_others = len(others)
    if n_others:
        prose += (
            f" The release also includes {n_others} other change"
            f"{'s' if n_others != 1 else ''}."
        )

    return DraftSummary(
        comment="<!-- DRAFT — please review and edit this summary -->",
        body=prose,
    )


def format_release_notes(notes: str, version: str) -> str:
    """Combine a header, the draft summary, and the GitHub-generated body."""
    summary = draft_summary(notes, version)
    # Keep the HTML comment on its own line; wrap only the prose body.
    body = textwrap.fill(summary.body, width=80) if summary.body else ""
    summary_block = f"{summary.comment}\n{body}" if body else summary.comment
    return f"# CBMC {version}\n\n{summary_block}\n\n{notes}\n"


def main():
    import argparse
    p = argparse.ArgumentParser(
        description="Generate draft CHANGELOG entry for a CBMC release"
    )
    p.add_argument("tag", help="Release tag, e.g. cbmc-6.8.0")
    p.add_argument("--previous", help="Previous release tag (auto-detected)")
    p.add_argument(
        "-o", "--output",
        help="Write to file instead of stdout",
    )
    args = p.parse_args()

    prev = args.previous or previous_tag(args.tag)
    ver = version_from_tag(args.tag)

    print(f"Generating notes for {args.tag} (since {prev})...",
          file=sys.stderr)

    notes = gh_generate_notes(args.tag, prev)
    output = format_release_notes(notes, ver)

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Written to {args.output}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
