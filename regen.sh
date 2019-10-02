#!/bin/sh
set -euo pipefail

DIR=`dirname $0`
cd ${DIR}

cargo run --bin gen_impl