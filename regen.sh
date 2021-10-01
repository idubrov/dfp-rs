#!/bin/sh
set -euo pipefail

DIR=`dirname $0`
cd ${DIR}

cargo run --package tool --bin gen_tests
cargo run --package tool --bin gen_impl