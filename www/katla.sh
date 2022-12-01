#!/bin/sh

find source -name "*.md" >tmp
while IFS= read -r rawfile; do
    file=$(echo "$rawfile" | sed "s|source/\(.*\)|\1|")
    filename=$(basename "$file" ".md")
    filedir=$(dirname "$file")
    htmldir="html/${filedir}"
    mdfile="${htmldir}/${filename}.md"
    htmlfile="${htmldir}/${filename}.html"
    mkdir -p "${htmldir}"
    idris2 -c "${rawfile}"
    ttc_version=$(ls build/ttc)
    katla markdown "$rawfile" "build/ttc/${ttc_version}/source/${filename}.ttm" >"$mdfile"
    markdown "$mdfile" >"$htmlfile"
    # rm "$mdfile"
done <tmp
rm tmp
