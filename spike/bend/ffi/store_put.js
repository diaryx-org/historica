// The JS twin of `store_put.c`: a file of lines written into the folder —
// its directory made, its text staged beside it and renamed over it, and a
// file it replaces keeping its permissions.
function store_put(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  const cut = query.indexOf("\n");
  if (cut < 0) return hist_fail(22, "a write is a path, then its text");
  const [file, text] = [query.slice(0, cut), query.slice(cut + 1)];
  const directory = path.dirname(file);
  try {
    fs.mkdirSync(directory, { recursive: true });
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${directory}: ${e.message}`);
  }
  let held = null;
  try {
    const entry = fs.lstatSync(file);
    if (entry.isFile()) held = entry.mode & 0o7777;
  } catch (_) {}
  const staged = `${file}.${process.pid}.staged`;
  try {
    fs.writeFileSync(staged, text, { flush: true });
    if (held !== null) fs.chmodSync(staged, held);
    fs.renameSync(staged, file);
  } catch (e) {
    try { fs.unlinkSync(staged); } catch (_) {}
    return hist_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
  }
  return io_done("written");
}
