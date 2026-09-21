// The JS twin of `store_digests.c`: the digest and the byte count of each
// file asked for, `- 0` where the file will not be read. `cache/` is not
// consulted, because the one caller is `check`.
function store_digests(query) {
  const fs = require("node:fs");
  const path = require("node:path");
  const crypto = require("node:crypto");
  const [root, ...paths] = query.split("\n");
  const answer = paths.map((relative) => {
    let bytes;
    try {
      bytes = fs.readFileSync(path.join(root, relative));
    } catch (_) {
      return "- 0";
    }
    return `${crypto.createHash("sha256").update(bytes).digest("hex")} ${bytes.length}`;
  });
  return io_done(answer.join("\n"));
}
