// The JS twin of `store_write.c`: a bookmark written — its directory made,
// its bytes staged beside it and renamed over it.
function store_write(query) {
  const fs = require("node:fs");
  const path = require("node:path");
  const cut = query.indexOf("\n");
  if (cut < 0) return io_fail(22, "a write is a path, then its bytes");
  const [file, bytes] = [query.slice(0, cut), query.slice(cut + 1)];
  const directory = path.dirname(file);
  try {
    fs.mkdirSync(directory, { recursive: true });
  } catch (e) {
    return io_fail(e.errno ? -e.errno : 5, `${directory}: ${e.message}`);
  }
  const staged = `${file}.${process.pid}.staged`;
  try {
    fs.writeFileSync(staged, bytes, { flush: true });
    fs.renameSync(staged, file);
  } catch (e) {
    try { fs.unlinkSync(staged); } catch (_) {}
    return io_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
  }
  return io_done("");
}
