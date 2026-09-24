// The JS twin of `store_real.c`: the current directory for an empty
// argument, and otherwise where the path really is, which only a path that
// exists has.
function store_real(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  if (query === "") return io_done(process.cwd());
  try {
    return io_done(fs.realpathSync.native(query));
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${query}: ${e.message}`);
  }
}
