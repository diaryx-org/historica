// The JS twin of `store_copy.c`: a folder's file filed once in the store,
// refused where its bytes no longer hash to the digest the survey found.
function store_copy(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  // The one way a store files bytes, which `store_once.js` says too:
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
  const fs = require("node:fs");
  const crypto = require("node:crypto");
  const lines = query.split("\n");
  if (lines.length !== 3) return hist_fail(22, "a copy is a path, where it goes, and its digest");
  const [from, to, wanted] = lines;
  let bytes;
  try {
    bytes = fs.readFileSync(from);
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${from}: ${e.message}`);
  }
  const found = crypto.createHash("sha256").update(bytes).digest("hex");
  if (found !== wanted) {
    return hist_fail(5, `the content for ${to} hashes to ${found} rather than ${wanted}, so nothing was written; it changed while it was being copied`);
  }
  return hist_once(hist_fail, to, bytes);
}
