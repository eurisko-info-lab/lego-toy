#!/bin/bash
# Run CoolTT tests with increased stack size to handle deep grammar recursion
ulimit -s 65536
exec lake exe lego-test-red --cooltt "$@"
