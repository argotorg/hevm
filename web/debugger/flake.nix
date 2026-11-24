{
  description = "Web page for hevm's interactive debugger";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    # the revision hevm uses, for the same tools
    nixpkgs.url = "github:nixos/nixpkgs/a595dde4d0d31606e19dcec73db02279db59d201";
  };

  outputs = { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          packages = [ pkgs.nodejs pkgs.typescript pkgs.esbuild ];
        };
      });
}
