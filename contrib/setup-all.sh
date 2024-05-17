#!/bin/bash

CONTRIB_DIR="$(dirname $0)"

$CONTRIB_DIR/setup-avr.sh
$CONTRIB_DIR/setup-boolector.sh
$CONTRIB_DIR/setup-btor2tools.sh
$CONTRIB_DIR/setup-pono.sh
$CONTRIB_DIR/setup-nuXmv.sh