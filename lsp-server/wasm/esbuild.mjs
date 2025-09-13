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

let watch = process.argv.includes("--watch") ? watchConfig : (entry) => false;
let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap_client = disable_sourcemap ? null : { sourcemap: true };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };

// Build of the VS Code wasm worker
let enableMeta = false;

function wasmBuild(file) {
  return esbuild
    .build({
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
      watch: watch(file),
    })
    .then((res) => {
      if(enableMeta) fs.writeFileSync('wacoq-meta.json', JSON.stringify(res.metafile, null, 2));
      console.log(`[watch] build finished for ${file}`);
    })
    .catch((err) => {
        console.log('error: ', err);
        process.exit(1);
    });
};

// Build of the WASM worker for VSCode
var wasmWorker = wasmBuild("./wacoq_worker.ts");

await Promise.all[wasmWorker];
