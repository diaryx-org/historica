// The JS twin of `store_chmod.c`: one file's execute bits set as its read
// bits say, and what the bit was before answered.
function store_chmod(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const cut = query.indexOf("\n");
  const runs = query.slice(cut + 1);
  if (cut < 0 || (runs !== "1" && runs !== "0")) return hist_fail(22, "a mode is a path, then `1` or `0`");
  const file = query.slice(0, cut);
  try {
    const held = fs.lstatSync(file).mode & 0o7777;
    const mode = runs === "1" ? held | ((held & 0o444) >> 2) : held & ~0o111;
    if (mode !== held) fs.chmodSync(file, mode);
    return io_done(held & 0o111 ? "1" : "0");
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
  }
}
