{
  perSystem = {
    config,
    pkgs,
    lib,
    inputs',
    ...
  }: {
    packages.vsix = (inputs'.napalm.legacyPackages).buildPackage ./. {
      installPhase = ''
        mkdir $out
        ${lib.getExe pkgs.vsce} package -o $out/$name.zip > /dev/null 2>&1
      '';
    };

    packages.vscode-extension = pkgs.vscode-utils.buildVscodeExtension rec {
      inherit (config.packages.vsix) name;

      vscodeExtPublisher = "ejgallego";
      vscodeExtName = name;

      vscodeExtUniqueId = "${vscodeExtPublisher}.${vscodeExtName}";

      src = "${config.packages.vsix}/${name}.zip";
    };

    devShells.client-vscode = pkgs.mkShell {
      packages = builtins.attrValues {
        inherit (pkgs) nodejs;
        inherit (pkgs.nodePackages) typescript typescript-language-server;
      };
    };

    treefmt.config.programs.prettier.enable = true;
  };
}
