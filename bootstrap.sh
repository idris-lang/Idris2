#!/bin/sh

make support
cp support/c/$IDRIS2_SUPPORT bootstrap/idris2-boot_app

cd bootstrap

sed s/libidris2_support.so/$IDRIS2_SUPPORT/g idris2sh_app/idris2sh.ss > idris2sh_app/idris2-boot.ss
sed -i "s|__PREFIX__|$2|g" idris2sh_app/idris2-boot.ss
$1 --script compile.ss

mkdir -p ../build/exec
mkdir -p ../build/exec/idris2sh_app
install idris2-boot ../build/exec/idris2sh
install idris2sh_app/* ../build/exec/idris2sh_app
