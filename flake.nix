{
  description = "Ambiente de desenvolvimento Haskell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          name = "haskell-dev";

          buildInputs = with pkgs; [
            pandoc
            ghc
            cabal-install
            haskell-language-server
            haskellPackages.fourmolu
            haskellPackages.hlint
            haskellPackages.hoogle
            haskellPackages.ghcid
            haskellPackages.cabal-fmt
            pkg-config
            zlib
            zlib.dev
          ];
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [
            pkgs.zlib
          ];
        };
      }
    );
}
