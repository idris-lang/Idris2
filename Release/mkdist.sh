#!/bin/sh

if [ $# -eq 0 ]
  then
    echo "No version number supplied"
    exit 1
fi

git clone https://github.com/idris-lang/Idris2.git
mv Idris2 Idris2-$1
cd Idris2-$1

# Go to the tag for the release we're making
git checkout tags/v$1

# Remove the directories and files we don't want in the release
rm -rf .git
rm -rf .github
rm .git*
rm -f .travis*
rm -rf Release
find . -type f -name '.gitignore' -exec rm -f {} \;

cd ..

tar zcf idris2-$1.tgz Idris2-$1

echo "idris2-$1.tgz created."
