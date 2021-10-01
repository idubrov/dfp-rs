#!/bin/sh
set -euxo pipefail
export DIR=`dirname $0`
diff -u "${DIR}/readtest.in" "${DIR}/readtest.patched.in" > "${DIR}/fixes.patch"
