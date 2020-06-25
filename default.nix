{ mkDerivation, base, containers, lens, mtl, stdenv }:
mkDerivation {
  pname = "Lambda-Cube";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [ base containers lens mtl ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
