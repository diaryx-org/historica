// The JS twin of `store_once.c`: bytes filed once under a name — the
// directory made, a file already there left alone where it holds these
// bytes and refused where it does not.
function store_once(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  // The one way a store files bytes, which `store_copy.js` says again:
  // each twin is its own scope.
  const hist_once = (hist_fail, file, bytes) => {
    const fs = require("node:fs");
    const path = require("node:path");
    const directory = path.dirname(file);
    try {
      fs.mkdirSync(directory, { recursive: true });
    } catch (e) {
      return hist_fail(e.errno ? -e.errno : 5, `${directory}: ${e.message}`);
    }
    try {
      fs.writeFileSync(file, bytes, { flag: "wx", flush: true });
      return io_done("written");
    } catch (e) {
      if (e.code !== "EEXIST") return hist_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
    }
    let existing;
    try {
      existing = fs.readFileSync(file);
    } catch (e) {
      return hist_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
    }
    if (!existing.equals(bytes)) return hist_fail(5, `${file} is named for a digest its bytes do not have`);
    return io_done("there");
  };
  const cut = query.indexOf("\n");
  if (cut < 0) return hist_fail(22, "a write is a path, then its bytes");
  return hist_once(hist_fail, query.slice(0, cut), Buffer.from(query.slice(cut + 1), "utf8"));
}
