// The JS twin of `store_folder.c`: one directory of the folder, an entry a
// line in byte order of name, each saying what it is without following it —
// `d`, `f <x> <size>`, `l` with the target on the next line, `L` for a
// target that cannot be spelled, `o` for anything else, `u` and its lossy
// spelling for a name that is not UTF-8. A name holding a newline is left
// out.
function store_folder(dir) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const fs = require("node:fs");
  const path = require("node:path");
  let names;
  try {
    names = fs.readdirSync(dir, { encoding: "buffer" });
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${dir}: ${e.message}`);
  }
  names.sort((a, b) => Buffer.compare(a, b));
  // Bun hands back a plain Uint8Array for `encoding: "buffer"`, whose
  // `toString` spells the bytes as decimals, so each is made a Buffer here.
  const spelled = (raw) => {
    const bytes = Buffer.from(raw.buffer, raw.byteOffset, raw.byteLength);
    const text = bytes.toString("utf8");
    return Buffer.from(text, "utf8").equals(bytes) ? text : null;
  };
  const lines = [];
  try {
    for (const bytes of names) {
      const name = spelled(bytes);
      if (name === null) {
        // `to_string_lossy`: each maximal ill-formed run one U+FFFD, which
        // is the decoder's own rule.
        const lossy = Buffer.from(bytes.buffer, bytes.byteOffset, bytes.byteLength).toString("utf8");
        if (!lossy.includes("\n")) lines.push(`u ${lossy}`);
        continue;
      }
      if (name.includes("\n")) continue;
      const full = path.join(dir, name);
      const entry = fs.lstatSync(full);
      if (entry.isSymbolicLink()) {
        const target = spelled(fs.readlinkSync(full, { encoding: "buffer" }));
        if (target === null || target.includes("\n")) lines.push(`L ${name}`);
        else lines.push(`l ${name}`, target);
      } else if (entry.isDirectory()) {
        lines.push(`d ${name}`);
      } else if (entry.isFile()) {
        lines.push(`f ${entry.mode & 0o111 ? 1 : 0} ${entry.size} ${name}`);
      } else {
        lines.push(`o ${name}`);
      }
    }
  } catch (e) {
    return hist_fail(e.errno ? -e.errno : 5, `${dir}: ${e.message}`);
  }
  return io_done(lines.join("\n"));
}
