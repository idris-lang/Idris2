#!/bin/bash

set -eu
set -o pipefail

prefix="../../libs"

find "$prefix" -name "*.idr" >tmp
while IFS= read -r rawfile; do
    file=${rawfile#../../libs/}
    libname="${file%%/*}"
    temp="${file#*/}"
    filename="${temp%.idr}"
    modulename="${filename//\//.}"
    htmldir="html/${libname}/source/"
    htmlfile="${htmldir}/${modulename}.html"
    mkdir -p "$htmldir"
    ttc_version=$(ls "${prefix}/${libname}/build/ttc/")
    katla html "$rawfile" "${prefix}/${libname}/build/ttc/${ttc_version}/${filename}.ttm" >"$htmlfile"
    sed -i "s|<head>|<head><title>${modulename}</title>|" "$htmlfile"
done <tmp
rm tmp

find "$prefix"/* -maxdepth 0 -type d >tmp
while IFS= read -r libdirectory; do
    libname="${libdirectory#"$prefix"/}"
    cp -r "$prefix"/"$libname"/build/docs/* html/"$libname"
    find html/"$libname"/docs/ -name "*.html" >tmp2
    while IFS= read -r file; do
        filename=$(basename "$file" ".html")
        sed -i "s|<h1>${filename}</h1>|<h1>${filename}<span style=\"float:right\">(<a href=\"../source/${filename}.html\">source</a>)</span></h1>|" "$file"
    done <tmp2
    rm tmp2
done <tmp
rm tmp
