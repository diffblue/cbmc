"""The coverage status of a line of source code.

The coverage status of a line is either HIT, PARTIAL, or MISSED.  One
line of code may generate many basic blocks of source code.  The
meaning of PARTIAL line status is that some of the basic blocks were
hit and some were missed.  It is common for the line status of a
statically unreachable line of code to be represented with None.
"""

MISSED = 0
HIT = 1
PARTIAL = 2


def combine(status1, status2):
    """Combine line status.  A HIT and a MISS combine to PARTIAL."""
    if status1 is None and status2 is None:
        return None

    if status1 is None:
        return status2
    if status2 is None:
        return status1

    if PARTIAL in [status1, status2]:
        return PARTIAL

    if status1 == status2:
        return status1

    return PARTIAL
