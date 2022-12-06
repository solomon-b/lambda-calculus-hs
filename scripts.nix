{s}: rec
{
  ghcidScript = s "dev" "ghcid --command 'cabal new-repl' --allow-eval --warnings";
  allScripts = [ghcidScript];
}
