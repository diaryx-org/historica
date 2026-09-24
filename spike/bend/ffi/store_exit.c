// The C side of `Store.exit`: the process ends with the code asked for,
// once what it printed is out, and says nothing more. Run on the event
// loop rather than a helper thread, since nothing comes after it.
#include <stdlib.h>

Term store_exit_run(Env e, Term* f, IoWork* w) {
  u64   n    = 0;
  char* text = io_cstr(e, f[0], &n);
  int   code = atoi(text);
  free(text);
  fflush(stdout);
  fflush(stderr);
  exit(code);
}

static void __attribute__((constructor)) store_exit_use(void) {
  io_eff(CID_STORE_EXIT, store_exit_run, 0);
}
