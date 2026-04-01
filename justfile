ormolu := "ormolu"
nixfmt := "nixpkgs-fmt"

# list available recipes
default:
    @just --list

# auto-format Haskell source code using ormolu
format-hs:
    {{ormolu}} --mode inplace $(git ls-files '*.hs' '*.hs-boot')

# auto-format Haskell source code using ormolu (changed files only)
format-hs-changed:
    #!/usr/bin/env bash
    files=$(git diff --diff-filter=d --name-only "$(git merge-base HEAD origin/main)" | grep '.*\.\(hs\|hs-boot\)$' || true)
    if [ -n "$files" ]; then
        {{ormolu}} --mode inplace $files
    fi

# check Haskell source code formatting using ormolu
check-format-hs:
    {{ormolu}} --mode check $(git ls-files '*.hs' '*.hs-boot')

# check Haskell source code formatting using ormolu (changed files only)
check-format-hs-changed:
    #!/usr/bin/env bash
    files=$(git diff --diff-filter=d --name-only "$(git merge-base HEAD origin/main)" | grep '.*\.\(hs\|hs-boot\)$' || true)
    if [ -n "$files" ]; then
        {{ormolu}} --mode check $files
    fi

# auto-format Nix source code using nixpkgs-fmt
format-nix:
    {{nixfmt}} $(git ls-files '*.nix' 'nix/*.nix')

# check Nix source code formatting using nixpkgs-fmt
check-format-nix:
    {{nixfmt}} --check $(git ls-files '*.nix' 'nix/*.nix')

# auto-format all source code
format: format-hs format-nix

# auto-format changed files
format-changed: format-hs-changed format-nix

# check all formatting
check-format: check-format-hs check-format-nix

# check formatting (changed files only)
check-format-changed: check-format-hs-changed check-format-nix

# build all executables
build:
    cabal build all

# clean build artifacts
clean:
    cabal clean

# run an interpreter (fzf picker, or pass a target directly)
[no-exit-message]
run target="":
    #!/usr/bin/env bash
    if [ -n "{{target}}" ]; then
        cabal run "{{target}}"
    else
        t=$(grep -oP '(?<=^executable )\d+\w*-\S+' lambda-calculus-hs.cabal | fzf --prompt="run> " --height=~20 --reverse) || exit 0
        cabal run "$t"
    fi

# run all numbered executables
run-all:
    #!/usr/bin/env bash
    for i in 00 01 02 03 04 05 06 07 08 09 10; do
        exe=$(cabal list-bin "$i-*" 2>/dev/null) && echo "=== $i ===" && $exe && echo
    done
