const browser = true
const env = {}
const cwd = () => "/";

// Doesn't work on coq-lsp setup, it does on jsCoq's
//
// export { browser as 'process.browser', env as 'process.env', cwd as 'process.cwd' }

// Working alternative
export const process = {
  browser,
  env,
  cwd
};
