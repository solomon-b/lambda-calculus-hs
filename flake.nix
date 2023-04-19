{
  description = "Single file Lambda Calculus implementations and presentation slides.";

  inputs = {
    # Nix Inputs
    nixpkgs.url = github:nixos/nixpkgs/22.11;
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
      compilerVersion = "ghc924";
      pkgs = nixpkgs.legacyPackages.${system};
      hsPkgs = pkgs.haskell.packages.${compilerVersion}.override {
        overrides = hfinal: hprev: {
          Lambda-Cube = hfinal.callCabal2nix "Lambda-Cube" ./. { };
        };
      };
    in
    rec {
      packages =
        utils.flattenTree
          { Lambda-Cube = hsPkgs.Lambda-Cube; };

      # nix develop
      devShell = hsPkgs.shellFor {
        withHoogle = true;
        packages = p: [
          p.Lambda-Cube
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
      defaultPackage = packages.Lambda-Cube;
    });
}
