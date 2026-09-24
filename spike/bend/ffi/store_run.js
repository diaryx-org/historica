// The JS twin of `store_run.c`: a program run to its end in a directory,
// with this process's standard streams, answering the code it exited with.
function store_run(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, in Rust's words, as the C
  // side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const failed = (errno) => hist_fail(errno, `${io_sys().strerror(errno)} (os error ${errno})`);
  const fs = require("node:fs");
  const path = require("node:path");
  const [directory, program, ...args] = query.split("\0");
  if (program === undefined) return hist_fail(22, "a run is a directory, then a program");
  // Found on `PATH` as `execvp` finds it, which is how the Rust tool's
  // `Command` finds it: a file there that is not runnable is passed over
  // and remembered, so that where nothing runnable is found the answer is
  // `EACCES` rather than "not found".
  let file = program;
  if (!program.includes("/")) {
    let denied = false;
    file = undefined;
    for (const entry of (process.env.PATH ?? "").split(":")) {
      const candidate = path.join(entry === "" ? "." : entry, program);
      let stat;
      try {
        stat = fs.statSync(candidate);
      } catch (_) {
        continue;
      }
      if (!stat.isFile()) continue;
      try {
        fs.accessSync(candidate, fs.constants.X_OK);
        file = candidate;
        break;
      } catch (_) {
        denied = true;
      }
    }
    if (file === undefined) return failed(denied ? 13 : 2);
  }
  const done = require("node:child_process").spawnSync(file, args, { cwd: directory, stdio: "inherit", argv0: program });
  if (done.error) return failed(done.error.errno ? -done.error.errno : 5);
  return io_done(done.status === null ? "signal" : String(done.status));
}
