// The JS twin of `store_runs.c`: a file's execute bits set as asked — made
// runnable, they follow the read bits; made plain, they go — and the answer
// says whether anything changed.
function store_runs(query) {
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const cut = query.indexOf("\n");
  const [path, wanted] = cut < 0 ? [query, ""] : [query.slice(0, cut), query.slice(cut + 1)];
  if (wanted !== "executable" && wanted !== "plain") return hist_fail(22, "a mode is a path, then `executable` or `plain`");
  try {
    const held = fs.statSync(path).mode & 0o7777;
    const mode = wanted === "executable" ? held | ((held & 0o444) >> 2) : held & ~0o111;
    if (mode === held) return io_done("held");
    fs.chmodSync(path, mode);
    return io_done("set");
  } catch (error) {
    return hist_fail(error.errno ? -error.errno : 5, path + ": " + error.message);
  }
}
