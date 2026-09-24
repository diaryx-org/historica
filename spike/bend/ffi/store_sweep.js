// The JS twin of `store_sweep.c`: every directory under the one named that
// holds nothing, removed deepest first, the one named kept, no link followed.
function store_sweep(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  let removed = 0;
  const sweep = (directory) => {
    let entries;
    try {
      entries = fs.readdirSync(directory, { withFileTypes: true });
    } catch (e) {
      if (e.code === "ENOENT") return true;
      throw { code: e.errno ? -e.errno : 5, message: `${directory}: ${e.message}` };
    }
    let empty = true;
    for (const entry of entries) {
      const inner = path.join(directory, entry.name);
      if (entry.isDirectory() && sweep(inner)) {
        try {
          fs.rmdirSync(inner);
        } catch (e) {
          throw { code: e.errno ? -e.errno : 5, message: `${inner}: ${e.message}` };
        }
        removed += 1;
      } else {
        empty = false;
      }
    }
    return empty;
  };
  try {
    sweep(query);
  } catch (e) {
    return hist_fail(e.code, e.message);
  }
  return io_done(String(removed));
}
