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

      passthru = let
        attrs = builtins.fromJSON (builtins.readFile ./package.json);
      in {
        extPublisher = attrs.publisher;
        extName = attrs.name;
        extVersion = attrs.version;
        extId = with attrs; "${publisher}.${name}";
      };
    };

    packages.vscode-extension = let
      vsix = config.packages.vsix;
    in
      pkgs.vscode-utils.buildVscodeExtension
      {
        inherit (vsix) name;

        version = vsix.extVersion;

        vscodeExtPublisher = vsix.extPublisher;
        vscodeExtName = vsix.extName;
        vscodeExtUniqueId = vsix.extId;

        src = "${vsix}/${vsix.name}.zip";
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
