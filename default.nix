{ mkDerivation, base, mtl, stdenv }:
mkDerivation {
  pname = "SimplyTypedPresentation";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [ base mtl ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
