// The JS twin of `store_list.c`: every file under `revisions/` and
// `operations/` — or under only the directories named after the root, one
// a line, which may be `names` or `skipped` too — relative to the root,
// sorted, one per line.
function store_list(query) {
  const fs = require("node:fs");
  const path = require("node:path");
  const [root, ...asked] = query.split("\n");
  const documents = ["revisions", "operations"];
  const listed = [...documents, "names", "skipped"];
  for (const dir of asked) {
    if (!listed.includes(dir)) return io_fail(22, `\`${dir}\` is not a directory this lists`);
  }
  const dirs = asked.length > 0 ? listed.filter((dir) => asked.includes(dir)) : documents;
  const paths = [];
  const walk = (dir) => {
    let entries;
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch (e) {
      if (e.code === "ENOENT") return;
      throw e;
    }
    for (const entry of entries) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(full);
      else {
        const rel = path.relative(root, full);
        if (!rel.includes("\n")) paths.push(rel);
      }
    }
  };
  try {
    for (const dir of dirs) walk(path.join(root, dir));
  } catch (e) {
    return io_fail(e.errno ? -e.errno : 5, `${root}: ${e.message}`);
  }
  // Byte order, as Rust's `sort` on `String`s is.
  paths.sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
  return io_done(paths.join("\n"));
}
