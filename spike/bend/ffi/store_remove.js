// The JS twin of `store_remove.c`: a bookmark removed, and each directory
// above it the removal left empty, up to the first line's.
function store_remove(query) {
  const fs = require("node:fs");
  const path = require("node:path");
  const cut = query.indexOf("\n");
  if (cut < 0) return io_fail(22, "a removal is where it stops, then the file");
  const [boundary, file] = [query.slice(0, cut), query.slice(cut + 1)];
  try {
    fs.unlinkSync(file);
  } catch (e) {
    if (e.code === "ENOENT") return io_done("absent");
    return io_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
  }
  for (let directory = path.dirname(file); directory !== boundary; directory = path.dirname(directory)) {
    try {
      fs.rmdirSync(directory);
    } catch (_) {
      break;
    }
  }
  return io_done("removed");
}
