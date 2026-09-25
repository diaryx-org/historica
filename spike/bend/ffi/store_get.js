// The JS twin of `store_get.c`: one text document over HTTP. The runtime's
// effects are synchronous and `fetch` is not, so the request is made by a
// child of this same runtime, which hands the body back whole; what came is
// answered as the C side answers it — `text` and the body where it is UTF-8,
// `bytes` and its digest where it is not, `status` and the code otherwise.
function store_get(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const { execFileSync } = require("node:child_process");
  const crypto = require("node:crypto");
  const child = `
    const said = (e) => { let whole = String(e && e.message || e); let c = e && e.cause; while (c) { whole += ": " + (c.message || c); c = c.cause; } return whole; };
    (async () => {
      try {
        const res = await fetch(process.env.HIST_URL, { cache: "no-store", redirect: "follow" });
        if (!res.ok) { process.stdout.write(JSON.stringify({ status: res.status })); return; }
        const body = Buffer.from(await res.arrayBuffer());
        process.stdout.write(JSON.stringify({ body: body.toString("base64") }));
      } catch (e) {
        process.stdout.write(JSON.stringify({ error: said(e) }));
      }
    })();`;
  let got;
  try {
    got = JSON.parse(execFileSync(process.execPath, ["-e", child], { env: { ...process.env, HIST_URL: query }, maxBuffer: 1 << 30 }).toString("utf8"));
  } catch (e) {
    return hist_fail(5, `${query}: ${e.message}`);
  }
  if (got.error !== undefined) return hist_fail(5, got.error);
  if (got.status !== undefined) return io_done(`status ${got.status}`);
  const body = Buffer.from(got.body, "base64");
  try {
    return io_done("text\n" + new TextDecoder("utf-8", { fatal: true }).decode(body));
  } catch (_) {
    return io_done("bytes " + crypto.createHash("sha256").update(body).digest("hex"));
  }
}
