HS_FILES = $(shell git ls-files '*.hs' '*.hs-boot')
CHANGED_HS_FILES = $(shell git diff --diff-filter=d --name-only `git merge-base HEAD origin/main` | grep '.*\(\.hs\|hs-boot\)$$')
NIX_FILES = $(shell git ls-files '*.nix' 'nix/*.nix')
SHELL_FILES = $(shell git ls-files '*.sh')
CHANGED_SHELL_FILES = $(shell git diff --diff-filter=d --name-only `git merge-base HEAD origin/main` | grep '.*\.sh$$')

NIX_FMT = nixpkgs-fmt
ORMOLU = ormolu
ORMOLU_VERSION = $(shell $(ORMOLU) --version | awk 'NR==1 { print $$2 }')

# Run Shellcheck with access to any file that's sourced, relative to the script's own directory
SHELLCHECK = shellcheck --external-sources --source-path=SCRIPTDIR

.PHONY: check-ormolu-version
check-ormolu-version:
	@if ! [ "$(ORMOLU_VERSION)" = "$(ORMOLU_CHECK_VERSION)" ]; then \
		echo "WARNING: ormolu version mismatch, expected $(ORMOLU_CHECK_VERSION) but got $(ORMOLU_VERSION)"; \
	fi

.PHONY: format-hs
## format-hs: auto-format Haskell source code using ormolu
format-hs: check-ormolu-version
	@echo running $(ORMOLU) --mode inplace
	@$(ORMOLU) --mode inplace $(HS_FILES)

.PHONY: format-hs-changed
## format-hs-changed: auto-format Haskell source code using ormolu (changed files only)
format-hs-changed: check-ormolu-version
	@echo running $(ORMOLU) --mode inplace
	@if [ -n "$(CHANGED_HS_FILES)" ]; then \
		$(ORMOLU) --mode inplace $(CHANGED_HS_FILES); \
	fi

.PHONY: check-format-hs
## check-format-hs: check Haskell source code formatting using ormolu
check-format-hs: check-ormolu-version
	@echo running $(ORMOLU) --mode check
	@$(ORMOLU) --mode check $(HS_FILES)

.PHONY: check-format-hs-changed
## check-format-hs-changed: check Haskell source code formatting using ormolu (changed-files-only)
check-format-hs-changed: check-ormolu-version
	@echo running $(ORMOLU) --mode check
	@if [ -n "$(CHANGED_HS_FILES)" ]; then \
		$(ORMOLU) --mode check $(CHANGED_HS_FILES); \
	fi

.PHONY: format-nix
## format-nix: auto-format Nix source code using `nixpkgs-fmt`
format-nix:
	@if command -v $(NIX_FMT) > /dev/null; then \
		echo "running $(NIX_FMT)"; \
		$(NIX_FMT) $(NIX_FILES); \
	else \
		echo "$(NIX_FMT) is not installed; skipping"; \
	fi

.PHONY: check-format-nix
## check-format-nix: check Nix source code using `nixpkgs-fmt`
check-format-nix:
	@if command -v $(NIX_FMT) > /dev/null; then \
		echo "running $(NIX_FMT) --check"; \
		$(NIX_FMT) --check $(NIX_FILES); \
	else \
		echo "$(NIX_FMT) is not installed; skipping"; \
	fi

.PHONY: format
format: format-hs format-nix

.PHONY: format-changed
format-changed: format-hs-changed format-nix

.PHONY: check-format
check-format: check-format-hs check-format-nix

.PHONY: check-format-changed
check-format-changed: check-format-hs-changed check-format-nix

.PHONY: lint-shell
## lint-shell: lint shell scripts using `shellcheck`
lint-shell:
	@echo running shellcheck
	@$(SHELLCHECK) $(SHELL_FILES)

.PHONY: lint-shell-changed
## lint-shell-changed: lint shell scripts using `shellcheck` (changed files only)
lint-shell-changed:
	@echo running shellcheck
	@if [ -n "$(CHANGED_SHELL_FILES)" ]; then \
		$(SHELLCHECK) $(CHANGED_SHELL_FILES); \
	fi

.PHONY: build-all
## build-all: build all haskell packages, or "have i broken anything?"
build-all: $(GENERATED_CABAL_FILES)
	cabal build all --enable-tests --enable-benchmarks

.PHONY: build-tests
## build-tests: build non-pro graphql executable tests
build-tests: $(GENERATED_CABAL_FILES)
	cabal build chat-bots-contrib-test 

.PHONY: clean
## build-tests: build non-pro graphql executable tests
clean: $(GENERATED_CABAL_FILES)
	cabal clean

.PHONY: test
## test-no-backends
# the leftover tests with no particular backend, like Remote Schemas
test: 
	cabal test all
