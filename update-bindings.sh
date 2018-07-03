#!/bin/sh

cargo install bindgen ; bindgen dfp-sys/src/bindings.h > dfp-sys/src/bindings.rs