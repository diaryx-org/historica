// The JS twin of `store_remove.c`: a bookmark removed, and each directory
// above it the removal left empty, up to the first line's.
function store_remove(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  const cut = query.indexOf("\n");
  if (cut < 0) return hist_fail(22, "a removal is where it stops, then the file");
  const [boundary, rest] = [query.slice(0, cut), query.slice(cut + 1)];
  // A third line is where tidying starts, where it is not the file.
  const next = rest.indexOf("\n");
  const [file, tidy] = next < 0 ? [rest, rest] : [rest.slice(0, next), rest.slice(next + 1)];
  try {
    fs.unlinkSync(file);
  } catch (e) {
    if (e.code === "ENOENT") return io_done("absent");
    return hist_fail(e.errno ? -e.errno : 5, `${file}: ${e.message}`);
  }
  for (let directory = path.dirname(tidy); directory !== boundary; directory = path.dirname(directory)) {
    try {
      fs.rmdirSync(directory);
    } catch (_) {
      break;
    }
  }
  return io_done("removed");
}
