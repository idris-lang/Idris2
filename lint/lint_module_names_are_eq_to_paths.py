#!/usr/bin/env python3

# reads lines of file
# skip empty lines or lines starting with a comment "||| " or "-- "
# first line should be "module My.Module"
# checks that module name is equal to path to file from the root

import sys
import subprocess
import re
import pprint

# Read lines until we find a line with the module declaration
def return_first_line_of_code(path_to_file):
    with open(path_to_file, "r") as f:
        # Skip empty lines or lines starting with "|||" or "--"
        for line in f:
            stripped_line = line.strip()
            if stripped_line and not stripped_line.startswith("|||") and not stripped_line.startswith("--"):
                line_with_a_module_name = stripped_line
                return line_with_a_module_name


def lint_module_names_eq_to_path(root, path_to_file_relative_to_root):
    path_to_file = root + "/" + path_to_file_relative_to_root
    try:
        line_with_a_module_name = return_first_line_of_code(path_to_file)
    except FileNotFoundError:
        print(f"Error: File '{path_to_file}' not found.")
        return False

    if not line_with_a_module_name or not line_with_a_module_name.startswith("module "):
        print(f"Error: No module declaration found in {path_to_file}")
        return False

    # Extract the declared module name
    module_name = line_with_a_module_name.split("module ", 1)[1]

    # Remove the root prefix and the '.idr' extension, then convert to module path format
    expected_module_name_from_path = path_to_file_relative_to_root.replace(".idr", "").replace("/", ".")

    # Check if the module name matches the expected name
    if module_name == expected_module_name_from_path:
        # print(f"Module name matches path for {path_to_file}")
        return True
    else:
        print(f"Error: Module name '{module_name}' does not expected module name '{expected_module_name_from_path}' for {path_to_file_relative_to_root}")
        return False

def quote_args_if_neeeded(args):
    quoted_args = []
    for arg in args:
        if " " in arg or "*" in arg:
            quoted_args.append(f'"{arg}"')
        else:
            quoted_args.append(arg)
    return quoted_args

def filter_out_matching(array, array_of_regexps):
    return [x for x in array if not any(re.match(r, x) for r in array_of_regexps)]

def get_all_idr_files(root):
    # Build the base command
    command = ["git", "ls-files", "*.idr"]

    print(f"Running command: {' '.join(quote_args_if_neeeded(command))}")

    # Get all `.idr` files tracked by git under the root directory
    result = subprocess.run(
        ["git", "ls-files", "*.idr"],
        text=True,
        capture_output=True,
        check=True,
        cwd=root,
    )
    idr_files = result.stdout.strip().splitlines()
    return idr_files

def lint_module_names_eq_to_path_root(root, idr_files):
    # Lint each file found
    n_total = len(idr_files)
    n_ok = 0
    n_fail = 0
    ok = True
    for idr_file in idr_files:
        result = lint_module_names_eq_to_path(root, idr_file)
        if result:
            n_ok += 1
        else:
            n_fail += 1
            ok = False

    return ok, n_total, n_ok, n_fail

# check that all files are from `list_of_known_root_dirs` and generate a dict { known_root_dir => relative_path_to_files }
# example:
# ```python
# known_files_dict, unknown_files_list = filepaths_to_dict_of_root_and_relative_paths(["src"], ["src/Data/Vect.idr", "unknown/Foo.idr"])
# assert known_files_dict == { "src": ["Data/Vect.idr"] }
# assert unknown_files_list == ["unknown/Foo.idr"]
# ```
def filepaths_to_dict_of_root_and_relative_paths(list_of_known_root_dirs, filepaths):
    def find_root_or_this_file(list_of_known_root_dirs, filepath):
        for root in list_of_known_root_dirs:
            if filepath.startswith(root + "/"):
                return root
        return False

    known_files_dict = {}
    unknown_files_list = []
    for filepath in filepaths:
        root_or_a_filepath = find_root_or_this_file(list_of_known_root_dirs, filepath)
        if root_or_a_filepath == False:
            unknown_files_list.append(filepath)
        else:
            relative_filepath = filepath[len(root_or_a_filepath)+1:]
            if root_or_a_filepath not in known_files_dict:
                known_files_dict[root_or_a_filepath] = []
            known_files_dict[root_or_a_filepath].append(relative_filepath)

    return known_files_dict, unknown_files_list

def main(list_of_regexes_to_exclude_files, list_of_known_root_dirs):
    # Get all `.idr` files tracked by git under the root directory
    try:
        idr_files = get_all_idr_files(".")
    except subprocess.CalledProcessError:
        print(f"Error: Unable to retrieve `.idr` files from cwd")
        sys.exit(1)

    idr_files_non_excluded = filter_out_matching(
        idr_files,
        list_of_regexes_to_exclude_files
    )

    # print(f"Found {len(idr_files_non_excluded)} non-excluded files")
    # print(f"Files: {idr_files_non_excluded}")

    # check that all files are from list_of_known_root_dirs and generate a dict { known_root_dir => relative_path_to_files }
    known_files_dict, unknown_files_list = filepaths_to_dict_of_root_and_relative_paths(
        list_of_known_root_dirs,
        idr_files_non_excluded
    )

    # print(f"Files: {pprint.pformat(known_files_dict)}")

    if len(unknown_files_list) > 0:
        print(f"Error: Unknown files, add them to `list_of_known_root_dirs` or `list_of_regexes_to_exclude_files`: {unknown_files_list}")
        sys.exit(1)

    # Iterate over each root directory and find `.idr` files
    ok = True
    for root, relative_path_to_files_in_root in known_files_dict.items():
        root_ok, n_total, n_ok, n_fail = lint_module_names_eq_to_path_root(root, relative_path_to_files_in_root)
        if root_ok:
            print(f"Linting successful for {root}, {n_ok}/{n_total} files OK")
        else:
            ok = False
            print(f"Error: Linting failed for {root}, {n_fail}/{n_total} files failed")

    if not ok:
      sys.exit(1)

if __name__ == "__main__":
    list_of_regexes_to_exclude_files = [
        r"^tests/([^/]+/){1,7}[^/]+\.idr$",
        r"^benchmark/benchmarks/[^/]+/[^/]+\.idr$",
        r"^nix/templates/.*\.idr$",
        r"^samples/.*\.idr$",
    ]
    list_of_known_root_dirs = [
        "src",
        "libs/base",
        "libs/contrib",
        "libs/linear",
        "libs/network",
        "libs/papers",
        "libs/prelude",
        "libs/test",
        "tests",
        "docs/source/cookbook"
    ]
    main(list_of_regexes_to_exclude_files, list_of_known_root_dirs)
