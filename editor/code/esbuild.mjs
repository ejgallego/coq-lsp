#!/usr/bin/env node

import * as esbuild from "esbuild";

esbuild
  .build({
    entryPoints: ["./src/client.ts"],
    bundle: true,
    sourcemap: true,
    format: "cjs",
    platform: "node",
    external: ["vscode"],
    outfile: "out/src/client.js",
  })
  .catch(() => process.exit(1));

esbuild
  .build({
    entryPoints: ["./view/infoview.ts"],
    bundle: true,
    sourcemap: "inline",
    platform: "browser",
    outfile: "view/out/index.js",
  })
  .catch(() => process.exit(1));
