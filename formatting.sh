#!/usr/bin/env bash
echo 'src/Dhall/Core/AST/Types/gen.dhall' | entr -c dhall format --inplace src/Dhall/Core/AST/Types/gen.dhall
