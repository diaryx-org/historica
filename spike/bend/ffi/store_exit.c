// The C side of `Store.exit`: the process ends with the code the Bend side
// decided, once everything it printed is out. The one effect with no Rust
// behind it, since ending the program is the C runtime's and nothing about
// a store comes into it.
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

Term store_exit_run(Env e, Term* f, IoWork* w) {
  u64 n; char* text = io_cstr(e, f[0], &n);
  int code = atoi(text);
  free(text);
  fflush(stdout);
  fflush(stderr);
  exit(code);
}

static void __attribute__((constructor)) store_exit_use(void) {
  io_eff(CID_STORE_EXIT, store_exit_run, 0);
}
