#!/usr/bin/env node
import process from "process";
import * as esbuild from "esbuild";

let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap_client = disable_sourcemap ? null : { sourcemap: true };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };

let enableMeta = false;

const plugins = [
  {
    name: "esbuild-problem-matcher",
    setup(build) {
      let file = build.initialOptions.entryPoints[0];

      build.onStart(() => {
        console.log(`[watch] build started for ${file}`);
      });

      build.onEnd((result) => {
        if (result.errors.length > 0) {
          result.errors.forEach((e) =>
            console.error(
              `> ${e.location.file}:${e.location.line}:${e.location.column}: error: ${e.text}`
            )
          );
        } else {
          console.log(`[watch] build finished for ${file}`);
          if (enableMeta) {
            fs.writeFileSync(
              `${file}.json`,
              JSON.stringify(result.metafile, null, 2)
            );
          }
        }
      });
    },
  },
];

const watchContext = async (ctxp) => {
  let ctx = await ctxp;

  if (process.argv.includes("--watch")) {
    await ctx.watch();
  } else {
    await ctx.rebuild();
    await ctx.dispose();
  }
};

// Build of the VS Code extension, for electron (hence cjs + node)
var node = watchContext(
  esbuild.context({
    entryPoints: ["./src/node.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "node",
    external: ["vscode"],
    outfile: "out/src/node.js",
    minify,
    plugins,
  })
);

var browser = watchContext(
  esbuild.context({
    entryPoints: ["./src/browser.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "browser",
    external: ["vscode"],
    outfile: "out/src/browser.js",
    minify,
    plugins,
  })
);

// Build of the VS Code view, for modern Chrome (webview)
function viewBuild(file) {
  return watchContext(
    esbuild.context({
      entryPoints: [file],
      bundle: true,
      ...sourcemap_view,
      platform: "browser",
      outdir: "out",
      outbase: ".",
      minify,
      plugins,
    })
  );
}

var infoView = viewBuild("./views/info/index.tsx");
var perfView = viewBuild("./views/perf/index.tsx");

await Promise.all[(node, browser, infoView, perfView)];
