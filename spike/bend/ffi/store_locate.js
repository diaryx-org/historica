// The JS twin of `store_locate.c`, for `bend main.bend` and the `.js` build:
// the same answer and the same complaint, from Bun's own filesystem.
function store_locate(from) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, in Rust's words for a
  // failure of the system's, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  let start;
  try {
    if (from === "") throw Object.assign(new Error("empty"), { errno: -2 });
    start = fs.realpathSync.native(from);
  } catch (e) {
    const errno = e.errno ? -e.errno : 5;
    return hist_fail(errno, `${from}: ${io_sys().strerror(errno)} (os error ${errno})`);
  }
  for (let dir = start; ; dir = path.dirname(dir)) {
    const candidate = path.join(dir, "history");
    try {
      if (fs.statSync(candidate).isDirectory()) return io_done(candidate);
    } catch (_) {}
    if (path.dirname(dir) === dir) break;
  }
  return hist_fail(2, "no `history` directory here or above " + start + "; `historica init` makes one");
}
