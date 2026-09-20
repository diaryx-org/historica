// The JS twin of `store_locate.c`, for `bend main.bend` and the `.js` build:
// the same answer and the same complaint, from Bun's own filesystem.
function store_locate(from) {
  const fs = require("node:fs");
  const path = require("node:path");
  let start;
  try {
    start = fs.realpathSync(from === "" ? "." : from);
  } catch (e) {
    return io_fail(e.errno ? -e.errno : 5, `${from}: ${e.message}`);
  }
  for (let dir = start; ; dir = path.dirname(dir)) {
    const candidate = path.join(dir, "history");
    try {
      if (fs.statSync(path.join(candidate, "historica.txt")).isFile()) return io_done(candidate);
    } catch (_) {}
    if (path.dirname(dir) === dir) break;
  }
  return io_fail(2, "no `history` directory here or above " + start + "; `historica init` makes one");
}
