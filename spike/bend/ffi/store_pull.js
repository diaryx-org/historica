// The JS twin of `store_pull.c`: one file over HTTP, into a file. A child
// of this same runtime makes the request and writes the body where it is
// told a piece at a time, hashing it as it passes, so nothing holds it
// whole; the answer is the digest and the size, or `status` and the code,
// having written nothing.
function store_pull(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const { execFileSync } = require("node:child_process");
  const cut = query.indexOf("\n");
  if (cut < 0) return hist_fail(22, "a pull is a URL, then where it goes");
  const [url, to] = [query.slice(0, cut), query.slice(cut + 1)];
  const child = `
    const fs = require("node:fs");
    const path = require("node:path");
    const crypto = require("node:crypto");
    const said = (e) => { let whole = String(e && e.message || e); let c = e && e.cause; while (c) { whole += ": " + (c.message || c); c = c.cause; } return whole; };
    const to = process.env.HIST_TO;
    (async () => {
      let res;
      try {
        res = await fetch(process.env.HIST_URL, { cache: "no-store", redirect: "follow" });
      } catch (e) {
        process.stdout.write(JSON.stringify({ error: said(e) }));
        return;
      }
      if (!res.ok) { process.stdout.write(JSON.stringify({ status: res.status })); return; }
      let out;
      try {
        fs.mkdirSync(path.dirname(to), { recursive: true });
        out = fs.openSync(to, "w");
      } catch (e) {
        process.stdout.write(JSON.stringify({ error: to + ": " + e.message, code: e.errno ? -e.errno : 5 }));
        return;
      }
      const hash = crypto.createHash("sha256");
      let size = 0;
      try {
        for await (const piece of res.body) {
          const bytes = Buffer.from(piece);
          hash.update(bytes);
          fs.writeSync(out, bytes);
          size += bytes.length;
        }
        fs.fsyncSync(out);
        fs.closeSync(out);
      } catch (e) {
        try { fs.closeSync(out); } catch (_) {}
        try { fs.unlinkSync(to); } catch (_) {}
        process.stdout.write(JSON.stringify({ error: said(e) }));
        return;
      }
      process.stdout.write(JSON.stringify({ digest: hash.digest("hex"), size }));
    })();`;
  let got;
  try {
    got = JSON.parse(execFileSync(process.execPath, ["-e", child], { env: { ...process.env, HIST_URL: url, HIST_TO: to } }).toString("utf8"));
  } catch (e) {
    return hist_fail(5, `${url}: ${e.message}`);
  }
  if (got.error !== undefined) return hist_fail(got.code || 5, got.error);
  if (got.status !== undefined) return io_done(`status ${got.status}`);
  return io_done(`${got.digest} ${got.size}`);
}
