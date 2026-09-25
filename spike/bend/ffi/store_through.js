// The JS twin of `store_through.c`: a file of lines written in place — its
// directory made, and its text written as `std::fs::write` writes, through
// a link standing at the path and into a file already there.
function store_through(query) {
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
  try {
    fs.writeFileSync(file, text);
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
  }
  return io_done("written");
}
