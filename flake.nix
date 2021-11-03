{
  description = "Interaction Nets";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  # inputs.lean.url = "github:leanprover/lean4";
  inputs.lean.url = github:leanprover/lean4-nightly/nightly-2021-10-30;
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, lean, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
        leanPkgs = lean.packages.${system};
        pkg = with pkgs;
          leanPkgs.buildLeanPackage.override (old1: {
            lean-vscode = old1.lean-vscode.override (old2: {
              vscodeExtensions = with vscode-extensions; [ vscodevim.vim ] ++ old2.vscodeExtensions;
            });
          }) {
            name = "MyPackage"; # must match the name of the top-level .lean file
            src = ./.;
          };
      in {
        packages = pkg // { inherit (leanPkgs) lean; };

        defaultPackage = pkg.modRoot;
      });
}
