#!/usr/bin/env sh

INPUT=`cat`

VERSION=`echo $INPUT | cut -d- -f1`
TAG=`echo $INPUT | cut -s -d- -f2`

MAJOR=`echo $VERSION | cut -d. -f1`
MINOR=`echo $VERSION | cut -d. -f2`
PATCH=`echo $VERSION | cut -d. -f3`

EXPECTED_LINE="(:return (:ok ((${MAJOR} ${MINOR} ${PATCH}) (\"${TAG}\"))) 1)"
EXPECTED_LENGTH=$(expr ${#EXPECTED_LINE} + 1) # +LF

sed -e "s/__EXPECTED_LINE__/$(printf '%06x' ${EXPECTED_LENGTH})${EXPECTED_LINE}/g" expected.in > expected
