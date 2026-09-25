// The JS twin of `store_runs.c`: the execute bits follow the read bits, and
// the answer says whether anything changed.
function store_runs(query) {
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  try {
    const held = fs.statSync(query).mode & 0o7777;
    const mode = held | ((held & 0o444) >> 2);
    if (mode === held) return io_done("held");
    fs.chmodSync(query, mode);
    return io_done("set");
  } catch (error) {
    return hist_fail(error.errno ? -error.errno : 5, query + ": " + error.message);
  }
}
