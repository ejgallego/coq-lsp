#!/usr/bin/env node
//@ts-check

import process from "process";
import * as esbuild from "esbuild";
import { createTextChangeRange } from "typescript";

// VSCode matcher plugin
const plugins = [{
  name: 'vscode-match',
  setup(build) {
    let entry = build.initialOptions.entryPoints[0];
    build.onStart(() => {
      console.log(`[watch] build started (rebuild for ${entry})`);
    });

    build.onEnd(result => {
      if (result.errors) {
        result.errors.forEach((error) =>
          console.error(
            `> ${error.location.file}:${error.location.line}:${error.location.column}: error: ${error.text}`,
          ),
        )
      } else {
          console.log(`[watch] build finished (rebuild for ${entry}`);
      }
    });
  }}];

// command line processing
let watch = process.argv.includes("--watch");
let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap_client = disable_sourcemap ? null : { sourcemap: true };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };

const nodeOptions = {
    entryPoints: ["./src/node.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "node",
    external: ["vscode"],
    outfile: "out/src/node.js",
    minify,
};

var browserOptions = {
    entryPoints: ["./src/browser.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "browser",
    external: ["vscode"],
    outfile: "out/src/browser.js",
    minify,
  };

  // Build of the VS Code view, for modern Chrome (webview)
function viewOptions(file) {
  return {
      entryPoints: [file],
      bundle: true,
      ...sourcemap_view,
      platform: "browser",
      outdir: "out",
      outbase: ".",
      minify,
    };
  };

var infoOptions = viewOptions("./views/info/index.tsx");
var perfOptions = viewOptions("./views/perf/index.tsx");

const ctxs = [nodeOptions, browserOptions, infoOptions, perfOptions].map((opts) =>
  //@ts-ignore
  esbuild.context({...opts, plugins }));
  
await Promise.all(ctxs.map((ctx) => {
    ctx.then((ctx) => {
      if(watch) {
        ctx.watch();
      } else {
        ctx.rebuild();
      }
    })
  }));

await Promise.all(ctxs.map((ctx) => ctx.then((ctx) => ctx.dispose())));
