// The JS twin of `store_mkdirs.c`: each directory named, a line each, made
// with every parent it lacks.
function store_mkdirs(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  for (const path of query.split("\n").filter((path) => path !== "")) {
    try {
      fs.mkdirSync(path, { recursive: true });
    } catch (e) {
      return hist_fail(e.errno ? -e.errno : 5, `${path}: ${e.message}`);
    }
  }
  return io_done("");
}
