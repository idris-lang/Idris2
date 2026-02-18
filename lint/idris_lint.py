#!/usr/bin/env python3
"""
Lint Idris source files for common issues.

This script scans the current directory and its subdirectories for Idris (.idr)
files and checks them for:
1. Trailing whitespace within lines.
2. Missing trailing newline at the end of file.
3. Too many trailing newlines at the end of file.
4. Invalid UTF-8 encoding in the file.
"""

import argparse
import os
import sys
from dataclasses import dataclass


@dataclass
class LintStats:
    """Statistics collected during linting."""

    files_checked: int = 0
    files_failed: int = 0
    trailing_whitespace: int = 0
    missing_newline: int = 0
    too_many_newlines: int = 0
    invalid_encoding: int = 0

    @property
    def total_issues(self) -> int:
        """Return the total number of issues found."""
        return self.trailing_whitespace + self.missing_newline + self.too_many_newlines

    @property
    def ok(self) -> bool:
        """Return True if no issues were found."""
        assert self.files_failed <= self.total_issues
        assert self.files_failed <= self.files_checked
        return self.total_issues == 0


def _lint_file(path: str, stats: LintStats) -> bool:
    """
    Check an individual file for linting violations.
    Args:
        path: The path to the file to be checked.
        stats: Statistics object to update.
    Returns:
        True if the file passed all checks, False otherwise.
    """
    try:
        with open(path, encoding="utf-8") as f:
            lines = f.readlines()
    except UnicodeDecodeError:
        print(f"Error reading {path}: Not UTF-8")
        stats.invalid_encoding += 1
        return False

    file_ok = True
    trailing_empty_lines = 1

    for line_no, line in enumerate(lines, start=1):
        line_without_newline = line.rstrip("\r\n")
        has_new_line = line_without_newline != line

        if line.isspace():
            trailing_empty_lines += has_new_line
        else:
            trailing_empty_lines = has_new_line

        if line_without_newline.endswith(" "):
            print(f"{path}:{line_no}: Trailing whitespace")
            stats.trailing_whitespace += 1
            file_ok = False

    if trailing_empty_lines == 0:
        print(f"{path}: Missing trailing newline")
        stats.missing_newline += 1
        return False

    if trailing_empty_lines > 1:
        print(f"{path}: Too many trailing newlines")
        stats.too_many_newlines += 1
        return False

    return file_ok


def main() -> None:
    """Scan the directory tree and lint all found Idris files."""
    parser = argparse.ArgumentParser(description="Idris Linter")
    parser.add_argument(
        "path",
        nargs="?",
        default=".",
        help="Directory to scan (default: current directory)",
    )
    args = parser.parse_args()

    stats = LintStats()

    for dirpath, _, filenames in os.walk(args.path):
        for filename in filenames:
            if not filename.endswith(".idr"):
                continue

            stats.files_checked += 1

            full_path = os.path.join(dirpath, filename)
            clean_path = os.path.normpath(full_path)

            if not _lint_file(clean_path, stats):
                stats.files_failed += 1

    # Sanity check
    if stats.files_checked == 0:
        print("Error: No .idr files found", file=sys.stderr)
        sys.exit(2)

    # Print summary
    print("-" * 30)
    print(f"Files checked:       {stats.files_checked}")
    print(f"Files with issues:   {stats.files_failed}")
    print("-" * 30)
    print(f"Trailing whitespace: {stats.trailing_whitespace}")
    print(f"Missing newlines:    {stats.missing_newline}")
    print(f"Too many newlines:   {stats.too_many_newlines}")
    print(f"Invalid encoding:    {stats.invalid_encoding}")
    print("-" * 30)
    print(f"Total issues:        {stats.total_issues}")
    print("-" * 30)

    if stats.ok:
        print(f"\n✓ {stats.files_checked} *.idr files are OK")
        sys.exit(0)
    else:
        print(f"\n✗ Issues found in {stats.files_failed} files")
        sys.exit(1)


if __name__ == "__main__":
    main()
