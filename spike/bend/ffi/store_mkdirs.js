// The JS twin of `store_mkdirs.c`: each directory named, a line each, made
// with every parent it lacks.
function store_mkdirs(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  // Rust's words for an OS error, `Display` of `std::io::Error`: the C
  // library's description and the code, which is what the native build
  // prints; Node's own are libuv's.
  const rust_words = (e) => {
    const words = { 1: "Operation not permitted", 2: "No such file or directory", 13: "Permission denied", 17: "File exists", 20: "Not a directory", 21: "Is a directory", 28: "No space left on device", 30: "Read-only file system", 36: "File name too long", 39: "Directory not empty", 40: "Too many levels of symbolic links" };
    const code = e.errno ? -e.errno : 0;
    return words[code] ? `${words[code]} (os error ${code})` : e.message;
  };
  const fs = require("node:fs");
  for (const path of query.split("\n").filter((path) => path !== "")) {
    try {
      fs.mkdirSync(path, { recursive: true });
    } catch (e) {
      return hist_fail(e.errno ? -e.errno : 5, `${path}: ${rust_words(e)}`);
    }
  }
  return io_done("");
}
