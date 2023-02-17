#!/bin/sh

prefix="../../libs"

find "$prefix" -name "*.idr" >tmp
while IFS= read -r rawfile; do
    file=$(echo "$rawfile" | sed "s|\.\./\.\./libs/\(.*\)|\1|")
    libname=$(echo "$file" | sed "s|\([^/]*\)/.*|\1|")
    filename=$(echo "$file" | sed "s|[^/]*/\(.*\)\.idr|\1|")
    modulename=$(echo "$filename" | sed "s|/|.|g")
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
    libname=$(echo "$libdirectory" | sed "s|$prefix/||")
    cp -r "$prefix"/"$libname"/build/docs/* html/"$libname"
    find html/"$libname"/docs/ -name "*.html" >tmp2
    while IFS= read -r file; do
        filename=$(basename "$file" ".html")
        sed -i "s|<h1>${filename}</h1>|<h1>${filename}<span style=\"float:right\">(<a href=\"../source/${filename}.html\">source</a>)</span></h1>|" "$file"
    done <tmp2
    rm tmp2
done <tmp
rm tmp
