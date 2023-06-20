/**
 * @type {import('@jest/types').Config.ProjectConfig}
 */
module.exports = {
  preset: "ts-jest",
  roots: ["<rootDir>"],
  testEnvironment: "node",
  transform: {
    "^.+\\.ts$": "ts-jest",
  },
  testRegex: "^.+\\.test\\.ts$",
  moduleFileExtensions: ["ts", "js", "node"],
};
