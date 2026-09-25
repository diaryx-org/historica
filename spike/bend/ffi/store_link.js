// The JS twin of `store_link.c`: a link made at a staged sibling and renamed
// over the path, the directories above it made first, its target never read.
function store_link(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  const cut = query.indexOf("\n");
  if (cut < 0) return hist_fail(22, "a link is a path, then where it points");
  const [at, target] = [query.slice(0, cut), query.slice(cut + 1)];
  const staged = path.join(path.dirname(at), path.basename(at) + "." + process.pid + ".staged");
  try {
    fs.mkdirSync(path.dirname(at), { recursive: true });
    fs.symlinkSync(target, staged);
    fs.renameSync(staged, at);
  } catch (error) {
    try { fs.unlinkSync(staged); } catch (_) {}
    return hist_fail(error.errno ? -error.errno : 5, at + ": " + error.message);
  }
  return io_done("linked");
}
