// The JS twin of `store_at.c`: where the bytes with each digest are, one
// path per digest asked for, `-` where the store holds none.
//
// `cache/operations.txt` accounts for the paths it names that the directory
// still holds; everything it does not account for is read and hashed. The
// rule is decision 0036's, and `../ffi/src/lib.rs` is the same answer.
function store_at(query) {
  const fs = require("node:fs");
  const path = require("node:path");
  const crypto = require("node:crypto");
  const [root, ...wanted] = query.split("\n");

  const held = store_walk(root);
  const at = new Map();
  const remember = (digest, relative) => {
    const there = at.get(digest);
    if (there === undefined || relative < there) at.set(digest, relative);
  };
  const accounted = new Set();
  let catalogue = "";
  try {
    catalogue = fs.readFileSync(path.join(root, "cache", "operations.txt"), "utf8");
  } catch (_) {}
  const lines = catalogue.split("\n");
  if (lines[0] === "historica-catalogue-1") {
    for (const line of lines.slice(1)) {
      const first = line.indexOf(" ");
      const second = line.indexOf(" ", first + 1);
      if (first !== 64 || second < 0) continue;
      const digest = line.slice(0, first);
      const relative = line.slice(second + 1);
      if (!held.has(relative)) continue;
      remember(digest, relative);
      accounted.add(relative);
    }
  }
  for (const relative of held) {
    if (accounted.has(relative)) continue;
    let bytes;
    try {
      bytes = fs.readFileSync(path.join(root, relative));
    } catch (_) {
      continue;
    }
    remember(crypto.createHash("sha256").update(bytes).digest("hex"), relative);
  }

  const sorted = [...at.keys()].sort();
  const answer = wanted.map((digest) => {
    if (digest === "") return "-";
    if (at.has(digest)) return at.get(digest);
    // The lesser path among the digests this prefix names, as Rust's is.
    let found = null;
    for (const key of sorted) {
      if (!key.startsWith(digest)) continue;
      const there = at.get(key);
      if (found === null || there < found) found = there;
    }
    return found === null ? "-" : found;
  });
  return io_done(answer.join("\n"));
}

// Every document the store holds, as paths relative to the root, sorted.
function store_walk(root) {
  const fs = require("node:fs");
  const path = require("node:path");
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
  for (const dir of ["revisions", "operations"]) walk(path.join(root, dir));
  // Byte order, as Rust's `sort` on `String`s is.
  paths.sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
  return new Set(paths);
}
