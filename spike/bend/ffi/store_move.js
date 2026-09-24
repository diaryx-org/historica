// The JS twin of `store_move.c`: a stated rename, done in the folder, and
// which of `moved`, `there`, `both` or `neither` it was. Whether a path is
// there follows links, as the Rust tool asks it.
function store_move(query) {
  const fs = require("node:fs");
  const path = require("node:path");
  const [folder, from, to, ...extra] = query.split("\n");
  if (to === undefined || extra.length) return io_fail(22, "a move is a folder, an old path and a new one");
  const [old, fresh] = [path.join(folder, from), path.join(folder, to)];
  const [was, is] = [fs.existsSync(old), fs.existsSync(fresh)];
  if (!was) return io_done(is ? "there" : "neither");
  if (is) return io_done("both");
  const directory = path.dirname(fresh);
  try {
    fs.mkdirSync(directory, { recursive: true });
  } catch (e) {
    return io_fail(e.errno ? -e.errno : 5, `${directory}: ${e.message}`);
  }
  try {
    fs.renameSync(old, fresh);
  } catch (e) {
    return io_fail(e.errno ? -e.errno : 5, `${from} -> ${to}: ${e.message}`);
  }
  return io_done("moved");
}
