#!/usr/bin/env node
import process from "process";
import * as esbuild from "esbuild";

let watchConfig = (entry) => {
  return {
    onRebuild(error, result) {
      console.log(`[watch] build started (rebuild for ${entry})`);
      if (error) {
        error.errors.forEach((error) =>
          console.error(
            `> ${error.location.file}:${error.location.line}:${error.location.column}: error: ${error.text}`
          )
        );
      } else console.log(`[watch] build finished (rebuild for ${entry}`);
    },
  };
};

let watch = process.argv.includes("--watch") ? watchConfig : (entry) => false;
let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap_client = disable_sourcemap ? null : { sourcemap: true };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };

// Build of the VS Code extension, for electron (hence cjs + node)
var node = esbuild
  .build({
    entryPoints: ["./src/node.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "node",
    external: ["vscode"],
    outfile: "out/src/node.js",
    minify,
    watch: watch("./src/node.ts"),
  })
  .then(() => {
    console.log("[watch] build finished for ./src/node.ts");
  })
  .catch(() => process.exit(1));

var browser = esbuild
  .build({
    entryPoints: ["./src/browser.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "browser",
    external: ["vscode"],
    outfile: "out/src/browser.js",
    minify,
    watch: watch("./src/browser.ts"),
  })
  .then(() => {
    console.log("[watch] build finished for ./src/browser.ts");
  })
  .catch(() => process.exit(1));

// Build of the VS Code view, for modern Chrome (webview)
function viewBuild(file) {
  return esbuild
    .build({
      entryPoints: [file],
      bundle: true,
      ...sourcemap_view,
      platform: "browser",
      outdir: "out",
      outbase: ".",
      minify,
      watch: watch(file),
    })
    .then(() => {
      console.log(`[watch] build finished for ${file}`);
    })
    .catch(() => process.exit(1));
}

var infoView = viewBuild("./views/info/index.tsx");
var perfView = viewBuild("./views/perf/index.tsx");

await Promise.all[(node, browser, infoView, perfView)];
