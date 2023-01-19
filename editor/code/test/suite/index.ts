import Jasmine = require("jasmine");
import * as path from "node:path";

const testsRoot = path.resolve(__dirname, "..");

export async function run(): Promise<void> {
  const jasmine = new Jasmine();
  jasmine.loadConfig({
    spec_dir: testsRoot,
    spec_files: ["**/*.test.js"],
  });
  jasmine.execute();
}
