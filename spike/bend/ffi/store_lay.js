// The JS twin of `store_lay.c`: a payload laid into the folder as a new
// file, refused where its bytes are not the digest asked for.
function store_lay(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  const crypto = require("node:crypto");
  const lines = query.split("\n");
  if (lines.length !== 3) return hist_fail(22, "a payload laid is where it is, where it goes, and its digest");
  const [from, to, wanted] = lines;
  let bytes;
  try {
    bytes = fs.readFileSync(from);
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${from}: ${e.message}`);
  }
  const found = crypto.createHash("sha256").update(bytes).digest("hex");
  if (found !== wanted) return hist_fail(5, `${from} holds ${found} rather than ${wanted}`);
  const directory = path.dirname(to);
  try {
    fs.mkdirSync(directory, { recursive: true });
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${directory}: ${e.message}`);
  }
  const staged = `${to}.${process.pid}.staged`;
  try {
    fs.writeFileSync(staged, bytes, { flush: true });
    fs.renameSync(staged, to);
  } catch (e) {
    try { fs.unlinkSync(staged); } catch (_) {}
    return hist_fail(e.errno ? -e.errno : 5, `${to}: ${e.message}`);
  }
  return io_done("written");
}
