// The JS twin of `store_exit.c`: the process ends with the code asked for.
// What was printed is already out, since every write here is synchronous.
function store_exit(query) {
  process.exit(Number(query) >>> 0);
}
