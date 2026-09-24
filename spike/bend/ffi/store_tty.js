// The JS twin of `store_tty.c`: `1` where standard output is a terminal.
function store_tty(query) {
  return io_done(process.stdout.isTTY ? "1" : "0");
}
