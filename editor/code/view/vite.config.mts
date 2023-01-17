import { defineConfig } from "vite";

export default defineConfig({
  build: {
    outDir: "out",
    sourcemap: "inline",
    rollupOptions: {
      output: {
        entryFileNames: `[name].js`,
        chunkFileNames: `[name].js`,
        assetFileNames: `[name].[ext]`,
      },
    },
  },
});
