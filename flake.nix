{
  description = "Simple haskell nix flake";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.11";

    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { flake-utils, nixpkgs, self }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        config = { };
        overlays = [ ];
        pkgs = import nixpkgs { inherit config overlays system; };
      in rec {
        devShell = pkgs.haskellPackages.shellFor {
          packages = p:
            [

            ];

          buildInputs = with pkgs.haskellPackages; [
            cabal-install

            # Helpful tools for `nix develop` shells
            #
            ghcid # https://github.com/ndmitchell/ghcid
            haskell-language-server # https://github.com/haskell/haskell-language-server
            hlint # https://github.com/ndmitchell/hlint
            ormolu # https://github.com/tweag/ormolu
            #brittany
          ];

          withHoogle = true;
        };
      });
}
