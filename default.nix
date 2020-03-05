{ mkDerivation, base, containers, mtl, stdenv }:
mkDerivation {
  pname = "SimplyTypedPresentation";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [ base containers mtl ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
