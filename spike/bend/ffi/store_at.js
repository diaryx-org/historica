// The JS twin of `store_at.c`: where the bytes with each digest are, one
// path per digest asked for, `-` where the store holds none — and, where
// the first line after the root is `forgets`, then each document that says
// it forgets one of them, as `<digest> <path>` a line, in path order.
//
// `cache/operations.txt` accounts for the paths it names that the directory
// still holds; everything it does not account for is read and hashed. The
// rule is decision 0036's, and `../ffi/src/lib.rs` is the same answer.
function store_at(query) {
  const fs = require("node:fs");
  const path = require("node:path");
  const crypto = require("node:crypto");
  const [root, ...asked] = query.split("\n");
  const standing = asked[0] === "forgets";
  const wanted = standing ? asked.slice(1) : asked;
  const forgetting = new Map();
  const forgets = (digest, relative) => {
    if (!forgetting.has(digest)) forgetting.set(digest, []);
    forgetting.get(digest).push(relative);
  };

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
      const forgotten = line.slice(first + 1, second);
      const relative = line.slice(second + 1);
      if (!held.has(relative)) continue;
      remember(digest, relative);
      if (forgotten.length === 64) forgets(forgotten, relative);
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
    // The first header of any of the three forgetting grammars.
    const opening = "historica\nforgets ";
    if (bytes.length > opening.length + 64 && bytes.subarray(0, opening.length).toString("latin1") === opening) {
      const digest = bytes.subarray(opening.length, opening.length + 64).toString("latin1");
      if (/^[0-9a-f]{64}$/.test(digest) && bytes[opening.length + 64] === 0x0a) forgets(digest, relative);
    }
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
  if (standing) {
    const beside = [];
    for (const digest of wanted) {
      for (const relative of forgetting.get(digest) || []) beside.push([relative, digest]);
    }
    // Byte order of the path, as Rust sorts its pairs.
    beside.sort((a, b) => Buffer.compare(Buffer.from(a[0]), Buffer.from(b[0])) || (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0));
    const seen = new Set();
    for (const [relative, digest] of beside) {
      const line = `${digest} ${relative}`;
      if (seen.has(line)) continue;
      seen.add(line);
      answer.push(line);
    }
  }
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
