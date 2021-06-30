#!/usr/bin/env bash
nearleyc $(dirname $0)/grammar.ne -o grammar.js
if [ -d .psci_modules ]; then
  cp grammar.js .psci_modules/grammar.js
fi
