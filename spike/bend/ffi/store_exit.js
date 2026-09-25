// The JS twin of `store_exit.c`: the process ends with the code asked for.
// What it printed is already out; the runtime writes synchronously.
function store_exit(query) {
  process.exit(Number(query));
}
