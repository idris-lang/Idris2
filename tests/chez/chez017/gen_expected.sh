#!/usr/bin/env sh
if [ $OS == "windows" ]; then
    MY_PWD="$(cygpath -m $(pwd) | sed -e 's#/#\\\\\\\\#g')\\\\\\\\" 
else
    MY_PWD=$(pwd)/
fi

sed -e "s|__PWD__|${MY_PWD}|g" expected.in > expected
