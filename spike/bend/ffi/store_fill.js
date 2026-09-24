// The JS twin of `store_fill.c`: the bytes asked for, as hex — drawn from
// `HISTORICA_PINNED_SEED`'s stream where one is pinned (SHA-256 of the seed
// and an eight-byte big-endian block counter, carried on across calls), and
// from the operating system's random source otherwise.
function store_fill(query) {
  // The runtime's `io_fail` keeps only a code and says the system's words
  // for it; this keeps what the refusal says, as the C side does.
  const hist_fail = (code, message) => ({ $: "Fail", error: io_tup(code >>> 0, String(message)) });
  const crypto = require("node:crypto");
  if (!/^[0-9]+$/.test(query)) return hist_fail(22, `\`${query}\` is not a count of bytes`);
  const count = Number(query);
  const seed = process.env.HISTORICA_PINNED_SEED;
  let bytes;
  if (seed === undefined) {
    bytes = crypto.randomBytes(count);
  } else {
    const drawn = (globalThis.hist_drawn ??= { block: 0n, held: [] });
    bytes = Buffer.alloc(count);
    for (let i = 0; i < count; i++) {
      if (drawn.held.length === 0) {
        const counter = Buffer.alloc(8);
        counter.writeBigUInt64BE(drawn.block);
        drawn.block += 1n;
        drawn.held = [...crypto.createHash("sha256").update(Buffer.from(seed, "utf8")).update(counter).digest()];
      }
      bytes[i] = drawn.held.shift();
    }
  }
  return io_done(bytes.toString("hex"));
}
