#!/bin/sh
set -euxo pipefail
export DIR=`dirname $0`
patch "${DIR}/readtest.in" --input="${DIR}/fixes.patch" --output="${DIR}/readtest.patched.in"
