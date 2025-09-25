#!/usr/bin/env node

import fs from 'fs';
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

let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap_client = disable_sourcemap ? null : { sourcemap: true };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };

// Build of the VS Code wasm worker
let enableMeta = false;

const plugins = [{
  name: 'esbuild-problem-matcher',
  setup(build) {
    let file = build.initialOptions.entryPoints[0];

    build.onStart(() => {
      console.log(`[watch] build started for ${file}`);
    });

    build.onEnd(result => {
      if(result.errors.length > 0) {
        result.errors.forEach((e) =>
          console.error(
            `> ${e.location.file}:${e.location.line}:${e.location.column}: error: ${e.text}`
          )
        );
      } else {
        console.log(`[watch] build finished for ${file}`);
        if (enableMeta) {
          fs.writeFileSync(`${file}.json`, JSON.stringify(result.metafile, null, 2));
        }
      }
    });
  },
}];

const watchContext = async (ctxp) => {

  let ctx = await ctxp;

  if (process.argv.includes("--watch")) {
    await ctx.watch();
  } else {
    await ctx.rebuild();
    await ctx.dispose();
  }
}

function wasmBuild(file) {
  return watchContext(esbuild.context({
    entryPoints: [file],
    bundle: true,
    platform: "browser",
    format: "iife",
    target: "es2020",
    outdir: "out",
    inject: [
      "./shims/process-shim.js",
      "./shims/buffer-shim.js",
    ],
    define: {
      global: "self",
    },
    metafile: enableMeta,
    // logLevel: 'debug',
    ...sourcemap_view,
    minify,
    plugins
  }));
}

// Build of the WASM worker for VSCode
var wasmWorker = wasmBuild("./wacoq_worker.ts");

await Promise.all[wasmWorker];
