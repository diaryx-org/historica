// The JS twin of `store_tidy.c`: the directory a moved file left, and each
// above it, removed until one holds something or the first line's is met.
function store_tidy(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  const cut = query.indexOf("\n");
  if (cut < 0) return hist_fail(22, "a tidying is where it stops, then the directory");
  const [boundary, start] = [query.slice(0, cut), query.slice(cut + 1)];
  let removed = 0;
  for (let directory = start; directory !== boundary; directory = path.dirname(directory)) {
    try {
      fs.rmdirSync(directory);
    } catch (_) {
      break;
    }
    removed += 1;
  }
  return io_done(String(removed));
}
