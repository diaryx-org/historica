// The JS twin of `store_now.c`: the pinned moment where
// `HISTORICA_PINNED_NOW` gives one, and otherwise the system clock in the
// local offset, to the second, spelled as the format spells a timestamp.
function store_now(query) {
  const pinned = process.env.HISTORICA_PINNED_NOW;
  if (pinned !== undefined) return io_done(pinned);
  const now = new Date();
  const two = (n) => String(n).padStart(2, "0");
  // `getTimezoneOffset` is minutes *behind* UTC, so its sign is the offset's
  // opposite.
  const ahead = -now.getTimezoneOffset();
  const sign = ahead < 0 ? "-" : "+";
  const offset = `${sign}${two(Math.floor(Math.abs(ahead) / 60))}:${two(Math.abs(ahead) % 60)}`;
  return io_done(
    `${String(now.getFullYear()).padStart(4, "0")}-${two(now.getMonth() + 1)}-${two(now.getDate())}` +
      `T${two(now.getHours())}:${two(now.getMinutes())}:${two(now.getSeconds())}${offset}`
  );
}
