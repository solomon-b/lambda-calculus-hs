{
  description = "Single file Lambda Calculus implementations and presentation slides.";

  inputs = {
    # Nix Inputs
    nixpkgs.url = github:nixos/nixpkgs/23.05;
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    ,
    }:
    let
      utils = flake-utils.lib;
    in
    utils.eachDefaultSystem (system:
    let
      compilerVersion = "ghc927";
      pkgs = nixpkgs.legacyPackages.${system};
      hsPkgs = pkgs.haskell.packages.${compilerVersion}.override {
        overrides = hfinal: hprev: {
          lambda-calculus-hs = hfinal.callCabal2nix "lambda-calculus-hs" ./. { };
        };
      };
    in
    rec {
      packages =
        utils.flattenTree
          { lambda-calculus-hs = hsPkgs.lambda-calculus-hs; };

      # nix develop
      devShell = hsPkgs.shellFor {
        withHoogle = true;
        packages = p: [
          p.lambda-calculus-hs
        ];
        buildInputs = with pkgs;
          [
            hsPkgs.haskell-language-server
            haskellPackages.cabal-install
            cabal2nix
            haskellPackages.ghcid
            haskellPackages.fourmolu
            haskellPackages.cabal-fmt
            nodePackages.serve
            nixpkgs-fmt
          ]
          ++ (builtins.attrValues (import ./scripts.nix { s = pkgs.writeShellScriptBin; }));
      };

      # nix build
      defaultPackage = packages.lambda-calculus-hs;
    });
}
